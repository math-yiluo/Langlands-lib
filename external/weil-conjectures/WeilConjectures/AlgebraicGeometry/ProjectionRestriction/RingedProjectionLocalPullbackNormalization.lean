/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionRestrictionDataSupplement
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.Derived.DerivedAdjunctionCochainUnit

/-! # Normalization of the localized pullback on complexes

## References

* Stacks Project, Tag 04J0 and Categories, the mates correspondence
* Stacks Project, Modules on Sites, Tag 04J0
* Cohomology on Sites, Tags 07A6 and 08FI
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.ProjectionRestriction

/-- The ordinary inverse adjunction mate of the specified direct-image square.
This constructs a natural transformation by the mates equivalence, without
choosing an inverse or assuming a tensor equation. -/
def localOrdinaryPullbackSquare
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ≅ R_X}
    {g : Global f R_Y R_X c} {V : Y.ProEt}
    (l : Local f R_Y R_X c g V) :
    SheafOfModules.overFunctor.{u + 1}
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_Y) V ⋙
        l.operation.pullback ⟶
      g.operation.pullback ⋙ SheafOfModules.overFunctor.{u + 1}
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_X)
        ((proEtaleBaseChange f).obj V) :=
  ((mateEquiv g.operation.moduleAdjunction l.operation.moduleAdjunction).symm
    (TwoSquare.mk _ _ _ _ l.ordinaryDirectImage.hom))

section OperationNormalization
variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
  [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} {R : Sheaf J CommRingCat.{u + 1}} {S : Sheaf K CommRingCat.{u + 1}}

private theorem rightComparison_eq (o : Operation F R S)
    (I : CochainComplex (Mod S) ℤ) :
    o.rightComparison I =
      (letI := o.kInjectives; o.pushforward.rightDerivedFunctorUnitQ I) := by
  let := o.kInjectives
  have h : DerivedCategory.Qh.map
      ((o.pushforward.mapHomotopyCategoryFactors (.up ℤ)).inv.app I) = 𝟙 _ := by
    change DerivedCategory.Qh.map (𝟙 _) = 𝟙 _
    exact DerivedCategory.Qh.map_id _
  simp only [Operation.rightComparison, derivedPushforwardComplexComparison, h,
    Functor.rightDerivedFunctorUnitQ, Operation.right]
  erw [Category.id_comp]

private def rightComparisonNatTrans (o : Operation F R S) :
    o.pushforward.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ o.right where
  app := o.rightComparison
  naturality I J h := by
    let := o.kInjectives
    change DerivedCategory.Q.map ((o.pushforward.mapHomologicalComplex (.up ℤ)).map h) ≫
        o.rightComparison J = o.rightComparison I ≫ o.right.map (DerivedCategory.Q.map h)
    rw [rightComparison_eq, rightComparison_eq]
    exact o.pushforward.rightDerivedFunctorUnitQ_naturality h

private theorem unit_normalized (o : Operation F R S) (P : CochainComplex (Mod R) ℤ) :
    o.derivedAdjunction.unit.app (DerivedCategory.Q.obj P) ≫
      o.right.map (o.leftModel.factors.hom.app P) =
    DerivedCategory.Q.map ((o.moduleAdjunction.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
      o.rightComparison ((o.pullback.mapHomologicalComplex (.up ℤ)).obj P) := by
  let := o.kInjectives
  rw [rightComparison_eq]
  exact CategoryTheory.derived_unit_cochain o.moduleAdjunction P

private theorem hom_normalized (o : Operation F R S)
    (P : CochainComplex (Mod R) ℤ) (I : CochainComplex (Mod S) ℤ)
    (h : (o.pullback.mapHomologicalComplex (.up ℤ)).obj P ⟶ I) :
    o.derivedAdjunction.homEquiv _ _
        (o.leftModel.factors.hom.app P ≫ DerivedCategory.Q.map h) =
      DerivedCategory.Q.map
          ((o.moduleAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv _ _ h) ≫
        o.rightComparison I := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, unit_normalized]
  have hn := (rightComparisonNatTrans o).naturality h
  change DerivedCategory.Q.map ((o.pushforward.mapHomologicalComplex (.up ℤ)).map h) ≫
      o.rightComparison I =
    o.rightComparison ((o.pullback.mapHomologicalComplex (.up ℤ)).obj P) ≫
      o.right.map (DerivedCategory.Q.map h) at hn
  rw [Category.assoc, ← hn]
  rw [← DerivedCategory.Q.map_comp_assoc, Adjunction.homEquiv_unit]

end OperationNormalization

private theorem directImage_normalized
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ≅ R_X}
    {g : Global f R_Y R_X c} {V : Y.ProEt}
    (l : Local f R_Y R_X c g V) (I : CochainComplex (Mod R_X) ℤ) :
    letI := l.restrictionYAdditive
    letI := l.restrictionXAdditive
    letI := l.leftRouteZero
    letI := l.rightRouteZero
    l.restrictionY.model.functor.map (g.operation.rightComparison I) ≫
        l.directImage.hom.app (DerivedCategory.Q.obj I) ≫
        l.operation.right.map (l.restrictionX.model.factors.hom.app I) =
      l.restrictionY.model.factors.hom.app
          ((g.operation.pushforward.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex l.ordinaryDirectImage (.up ℤ)).hom.app I) ≫
        l.operation.rightComparison
          ((SheafOfModules.overFunctor.{u + 1}
            ((sheafCompose (ProEt.topology X)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_X)
            ((proEtaleBaseChange f).obj V)).mapHomologicalComplex (.up ℤ) |>.obj I) := by
  let := l.restrictionYAdditive
  let := l.restrictionXAdditive
  let := l.leftRouteZero
  let := l.rightRouteZero
  let := g.operation.kInjectives
  let := l.restrictionX.limits
  let := l.restrictionX.colimits
  let G := SheafOfModules.overFunctor.{u + 1}
    ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_Y) V
  let H := SheafOfModules.overFunctor.{u + 1}
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_X)
    ((proEtaleBaseChange f).obj V)
  let B := g.operation.pushforward.mapHomologicalComplex (.up ℤ)
  let Hc := H.mapHomologicalComplex (.up ℤ)
  let target := Hc ⋙ DerivedCategory.Q ⋙ l.operation.right
  let a : B ⋙ DerivedCategory.Q ⋙ l.restrictionY.model.functor ⟶ target :=
    Functor.whiskerRight (rightComparisonNatTrans g.operation) l.restrictionY.model.functor ≫
      Functor.whiskerLeft DerivedCategory.Q l.directImage.hom ≫
      Functor.whiskerRight l.restrictionX.model.factors.hom l.operation.right
  let b : B ⋙ DerivedCategory.Q ⋙ l.restrictionY.model.functor ⟶ target :=
    Functor.whiskerLeft B l.restrictionY.model.factors.hom ≫
      Functor.whiskerRight
        (NatIso.mapHomologicalComplex l.ordinaryDirectImage (.up ℤ)).hom DerivedCategory.Q ≫
      Functor.whiskerLeft Hc (rightComparisonNatTrans l.operation)
  obtain ⟨J, hJ, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective I
  have := hj
  have : QuasiIso (Hc.map j) := inferInstance
  have : IsIso (target.map j) := by
    change IsIso (l.operation.right.map (DerivedCategory.Q.map (Hc.map j)))
    infer_instance
  change a.app I = b.app I
  apply (cancel_mono (target.map j)).1
  rw [← a.naturality j, ← b.naturality j]
  congr 1
  have hn := congrArg
    (fun z ↦ z ≫ l.operation.right.map (l.restrictionX.model.factors.hom.app J))
    (l.directImage_representative J hJ)
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app] at hn
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hn
  exact hn

private theorem normalize
    {A B Av Bv DA DB DAv DBv : Type*}
    [Category A] [Category B] [Category Av] [Category Bv]
    [Category DA] [Category DB] [Category DAv] [Category DBv]
    {G : A ⥤ B} {F : B ⥤ A} {Gv : Av ⥤ Bv} {Fv : Bv ⥤ Av}
    (adj : G ⊣ F) (adjv : Gv ⊣ Fv)
    (rA : A ⥤ Av) (rB : B ⥤ Bv)
    (QA : A ⥤ DA) (QB : B ⥤ DB) (QAv : Av ⥤ DAv) (QBv : Bv ⥤ DBv)
    {L : DA ⥤ DB} {R : DB ⥤ DA} {Lv : DAv ⥤ DBv} {Rv : DBv ⥤ DAv}
    (d : L ⊣ R) (dv : Lv ⊣ Rv)
    (jA : DA ⥤ DAv) (jB : DB ⥤ DBv)
    (cA : QA ⋙ jA ≅ rA ⋙ QAv) (cB : QB ⋙ jB ≅ rB ⋙ QBv)
    (epsilon : QA ⋙ L ⟶ G ⋙ QB) (eta : F ⋙ QA ⟶ QB ⋙ R)
    (epsilonv : QAv ⋙ Lv ⟶ Gv ⋙ QBv) (etav : Fv ⋙ QAv ⟶ QBv ⋙ Rv)
    (lambda : jA ⋙ Lv ⟶ L ⋙ jB) (beta : R ⋙ jA ⟶ jB ⋙ Rv) (P : A)
    (tau : rA.obj (F.obj (G.obj P)) ⟶ Fv.obj (rB.obj (G.obj P)))
    (lam : Gv.obj (rA.obj P) ⟶ rB.obj (G.obj P))
    (hu : jA.map (d.unit.app (QA.obj P)) ≫ beta.app (L.obj (QA.obj P)) =
      dv.unit.app (jA.obj (QA.obj P)) ≫ Rv.map (lambda.app (QA.obj P)))
    (hlam : adjv.homEquiv _ _ lam = rA.map (adj.unit.app P) ≫ tau)
    (hunit : d.unit.app (QA.obj P) ≫ R.map (epsilon.app P) =
      QA.map (adj.unit.app P) ≫ eta.app (G.obj P))
    (hnormal : jA.map (eta.app (G.obj P)) ≫ beta.app (QB.obj (G.obj P)) ≫
        Rv.map (cB.hom.app (G.obj P)) =
      cA.hom.app (F.obj (G.obj P)) ≫ QAv.map tau ≫ etav.app (rB.obj (G.obj P)))
    (hlocal : dv.homEquiv _ _ (epsilonv.app (rA.obj P) ≫ QBv.map lam) =
      QAv.map (adjv.homEquiv _ _ lam) ≫ etav.app (rB.obj (G.obj P))) :
    lambda.app (QA.obj P) ≫ jB.map (epsilon.app P) ≫ cB.hom.app (G.obj P) =
      Lv.map (cA.hom.app P) ≫ epsilonv.app (rA.obj P) ≫ QBv.map lam := by
  apply (dv.homEquiv _ _).injective
  rw [dv.homEquiv_naturality_left]
  dsimp only [Functor.comp_obj]
  rw [hlocal, Adjunction.homEquiv_unit]
  simp only [Rv.map_comp, ← Category.assoc]
  rw [← hu]
  simp only [Category.assoc]
  have hn := beta.naturality (epsilon.app P)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  slice_lhs 2 3 => rw [← hn]
  simp only [← Category.assoc]
  rw [← jA.map_comp, hunit, jA.map_comp]
  simp only [Category.assoc]
  rw [hnormal]
  have hc := cA.hom.naturality (adj.unit.app P)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hc
  rw [← Category.assoc, ← Category.assoc, hc]
  simp only [Category.assoc, ← QAv.map_comp, hlam, Functor.id_obj]

/-- The derived square, conjugated by the exact localization comparisons, is
localization of the ordinary inverse mate on every complex. -/
theorem localPullbackNormalization
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ≅ R_X)
    (g : Global f R_Y R_X c) (V : Y.ProEt)
    (l : Local f R_Y R_X c g V) :
    letI := l.restrictionYAdditive
    letI := l.restrictionXAdditive
    ∀ P : CochainComplex (Mod R_Y) ℤ,
      l.pullback.inv.app (DerivedCategory.Q.obj P) ≫
        l.restrictionX.model.functor.map (g.operation.leftModel.factors.hom.app P) ≫
        l.restrictionX.model.factors.hom.app
          ((g.operation.pullback.mapHomologicalComplex (.up ℤ)).obj P) =
      l.operation.left.map (l.restrictionY.model.factors.hom.app P) ≫
        l.operation.leftModel.factors.hom.app
          ((SheafOfModules.overFunctor.{u + 1}
            ((sheafCompose (ProEt.topology Y)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_Y) V).mapHomologicalComplex
              (.up ℤ) |>.obj P) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (localOrdinaryPullbackSquare l) (.up ℤ)).app P) := by
  let := l.restrictionYAdditive
  let := l.restrictionXAdditive
  let := l.leftRouteZero
  let := l.rightRouteZero
  let rY := SheafOfModules.overFunctor.{u + 1}
    ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_Y) V
  let rX := SheafOfModules.overFunctor.{u + 1}
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_X)
    ((proEtaleBaseChange f).obj V)
  let rYc := rY.mapHomologicalComplex (.up ℤ)
  let rXc := rX.mapHomologicalComplex (.up ℤ)
  let Fc := g.operation.pullback.mapHomologicalComplex (.up ℤ)
  let adj := g.operation.moduleAdjunction.mapHomologicalComplex (.up ℤ)
  let adjv := l.operation.moduleAdjunction.mapHomologicalComplex (.up ℤ)
  let sd := TwoSquare.mk l.restrictionY.model.functor g.operation.left
    l.operation.left l.restrictionX.model.functor l.pullback.inv
  have hm : (mateEquiv g.operation.derivedAdjunction l.operation.derivedAdjunction sd) =
      l.directImage.hom := by
    apply NatTrans.ext
    funext E
    apply (l.operation.derivedAdjunction.homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
    exact (mateEquiv_counit g.operation.derivedAdjunction l.operation.derivedAdjunction
      sd E).trans (l.mate_counit E).symm
  intro P
  let sigma := (NatTrans.mapHomologicalComplex (localOrdinaryPullbackSquare l) (.up ℤ)).app P
  let tau := (NatIso.mapHomologicalComplex l.ordinaryDirectImage (.up ℤ)).hom.app (Fc.obj P)
  apply normalize adj adjv rYc rXc
    DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
    g.operation.derivedAdjunction l.operation.derivedAdjunction
    l.restrictionY.model.functor l.restrictionX.model.functor
    l.restrictionY.model.factors l.restrictionX.model.factors
    g.operation.leftModel.factors.hom (rightComparisonNatTrans g.operation)
    l.operation.leftModel.factors.hom (rightComparisonNatTrans l.operation)
    l.pullback.inv l.directImage.hom P tau sigma
  · have hu := unit_mateEquiv g.operation.derivedAdjunction l.operation.derivedAdjunction
      sd (DerivedCategory.Q.obj P)
    change l.restrictionY.model.functor.map
        (g.operation.derivedAdjunction.unit.app (DerivedCategory.Q.obj P)) ≫
        (mateEquiv g.operation.derivedAdjunction l.operation.derivedAdjunction sd).app
          (g.operation.left.obj (DerivedCategory.Q.obj P)) = _ at hu
    rw [hm] at hu
    exact hu
  · rw [Adjunction.homEquiv_unit]
    apply HomologicalComplex.hom_ext
    intro n
    change l.operation.moduleAdjunction.unit.app ((P.X n).over V) ≫
        l.operation.pushforward.map ((localOrdinaryPullbackSquare l).app (P.X n)) =
      rY.map (g.operation.moduleAdjunction.unit.app (P.X n)) ≫
        l.ordinaryDirectImage.hom.app (g.operation.pullback.obj (P.X n))
    exact (unit_mateEquiv_symm g.operation.moduleAdjunction l.operation.moduleAdjunction
      (TwoSquare.mk _ _ _ _ l.ordinaryDirectImage.hom) (P.X n)).symm
  · exact unit_normalized g.operation P
  · exact directImage_normalized l (Fc.obj P)
  · exact hom_normalized l.operation (rYc.obj P) (rXc.obj (Fc.obj P)) sigma

end AlgebraicGeometry.Scheme.ProjectionRestriction
