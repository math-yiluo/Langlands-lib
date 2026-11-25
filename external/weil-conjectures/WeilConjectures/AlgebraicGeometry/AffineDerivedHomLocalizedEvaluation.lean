/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.AlgebraicGeometry.AffineHomKInjectiveEvaluation
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives

/-! # Localization of the affine sheaf-Hom evaluation counit

Source: Stacks Project, duality.tex, Tags 0BV0 and 0AX3.
-/

@[expose] public section

universe u wY wA

open CategoryTheory Opposite AlgebraicGeometry

namespace AlgebraicGeometry

/-- An additive functor's localized comparison is invertible on K-injective complexes. -/
private theorem comparison_isIso_on_kInjective
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (H : C ⥤ D) [H.Additive]
    (R : DerivedCategory C ⥤ DerivedCategory D)
    (β : H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R)
    (hR : R.IsRightDerivedFunctor β (HomologicalComplex.quasiIso C (.up ℤ)))
    (I : CochainComplex C ℤ) [I.IsKInjective] : IsIso (β.app I) := by
  have := hR
  have h : (CochainComplex.KInjectives.localizerMorphism C).Derives
      (H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) := by
    intro A B g hg
    have : QuasiIso g.hom := hg
    have : A.obj.IsKInjective := A.property
    have : B.obj.IsKInjective := B.property
    have he := (CochainComplex.IsKInjective.quasiIso_iff g.hom).mp inferInstance
    obtain ⟨e, he⟩ := he
    change IsIso (DerivedCategory.Q.map ((H.mapHomologicalComplex (.up ℤ)).map g.hom))
    rw [← he]
    have : QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map e.hom) :=
      (H.mapHomotopyEquiv e).quasiIso_hom
    infer_instance
  exact h.isIso_of_isRightDerivedFunctor β (CochainComplex.KInjectives.mk I)


/-- Transport a comparison respecting a natural evaluation map along an isomorphism. -/
private theorem transport_evaluation
    {C : Type*} [Category C] (P G H : C ⥤ C) (ε : P ⟶ 𝟭 C)
    (v : G ⟶ H) (j : H ≅ 𝟭 C) {X Y : C} (q : X ≅ Y)
    (d : P.obj Y ≅ G.obj Y)
    (hd : d.hom ≫ v.app Y ≫ j.hom.app Y = ε.app Y) :
    ∃ e : P.obj X ≅ G.obj X, e.hom ≫ v.app X ≫ j.hom.app X = ε.app X := by
  refine ⟨P.mapIso q ≪≫ d ≪≫ G.mapIso q.symm, ?_⟩
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  simp only [Category.assoc]
  rw [← Category.assoc (G.map q.inv), v.naturality q.inv, Category.assoc,
    j.hom.naturality q.inv]
  have hd' := congrArg (fun z ↦ z ≫ q.inv) hd
  simp only [Category.assoc] at hd'
  change P.map q.hom ≫ (d.hom ≫ v.app Y ≫ j.hom.app Y ≫ q.inv) = _
  rw [hd', ← Category.assoc, ε.naturality q.hom]
  simp

/-- A change of the unit-Hom isomorphism is absorbed by an automorphism of the target. -/
private theorem change_evaluation_iso
    {C : Type*} [Category C] (G H : C ⥤ C) (v : G ⟶ H)
    (j ι : H ≅ 𝟭 C) {X Z : C} (d : Z ≅ G.obj X) (ε : Z ⟶ X)
    (hd : d.hom ≫ v.app X ≫ j.hom.app X = ε) :
    ∃ e : Z ≅ G.obj X, e.hom ≫ v.app X ≫ ι.hom.app X = ε := by
  let α : X ≅ X := (ι.app X).symm ≪≫ j.app X
  refine ⟨d ≪≫ G.mapIso α, ?_⟩
  dsimp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [Category.assoc, ← Category.assoc (G.map α.hom), v.naturality α.hom,
    Category.assoc, ι.hom.naturality α.hom]
  simp [α, ← Category.assoc, hd]

/-- Evaluation compatibility on complex representatives for an already supplied derived
sheaf-Hom adjunction. This does not construct the adjunction or the unit-Hom isomorphism.

Source: Stacks Project, duality.tex, Tags 0BUZ, 0BV0 and 0AX3.
(blueprint: lem-sc-affine-derived-hom-localized-evaluation).

Proof:
1. Replace the complex K by a K-injective resolution I. The right-derived universal
   property identifies R(Q K) with Q_A(H(I)); exact scalar restriction identifies its
   image under L with Q(H(I) restricted to O_Y).
2. Apply iH termwise. The underlying module of the algebra unit is f_* O_X, with the
   identification equal to the identity on sections. The derivedInternalHom localization
   comparison now identifies the resulting object with RHom(f_* O_X, Q K).
3. The equality h_eval says on every open that the underived counit evaluates at one.
   Under iH it is precomposition by O_Y -> f_* O_X followed by evaluation at one.
   This equality holds degreewise and therefore as a chain map. The equality h_counit
   identifies its image under Q with the derived counit; evaluate on I and cancel the
   invertible resolution comparisons.
4. With the canonical unit-Hom identification this gives the asserted equality.
   For the given iota, compose the comparison in step 2 with RHom(f_* O_X, alpha),
   where alpha is iota.inv followed by canonical_iota.hom. Naturality gives
   RHom(O_Y, alpha) followed by iota = iota followed by alpha, so the extra
   factor canonical_iota.inv followed by iota followed by alpha cancels to the
   identity. Thus the result is independent of the chosen unit-Hom isomorphism. -/
theorem affine_derivedHom_localized_evaluation
    {Y X : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wA}
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))]
    (H : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))
      [H.Additive]
      (iH : H ⋙ SheafOfModules.restrictScalars
          (R := moduleRings Y.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩ ≅
        (SheafOfModules.homFunctor Y.sheaf).obj
          (op ((SheafOfModules.restrictScalars
            (R := moduleRings Y.toRingedSpace)
            (R' := moduleRings (directImageAlgebraSpace f))
            ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).obj
              (SheafOfModules.unit (moduleRings (directImageAlgebraSpace f))))))
      (adj₀ : SheafOfModules.restrictScalars
          (R := moduleRings Y.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩ ⊣ H)
    (h_eval : ∀ (F : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (U : Y.Opens)
          (φ : (H.obj F).val.obj (op U)),
        ((adj₀.counit.app F).val.app (op U)).hom φ =
          ((((iH.hom.app F).val.app (op U)).hom φ).app (op (Over.mk (𝟙 U)))).hom
            (1 : (moduleRings (directImageAlgebraSpace f)).obj.obj (op U)))
    (R : schemeDerivedCategory Y ⥤
          DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f))))
        (β : H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R)
        (L : DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f))) ⥤
          schemeDerivedCategory Y)
        (t : DerivedCategory.Q ⋙ L ≅
          (SheafOfModules.restrictScalars
            (R := moduleRings Y.toRingedSpace)
            (R' := moduleRings (directImageAlgebraSpace f))
            ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).mapHomologicalComplex
              (.up ℤ) ⋙ DerivedCategory.Q)
        (adj : L ⊣ R)
    (hR : R.IsRightDerivedFunctor β (HomologicalComplex.quasiIso _ (.up ℤ)))
    (h_counit : ∀ K : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
          L.map (β.app K) ≫ adj.counit.app (DerivedCategory.Q.obj K) =
            t.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj K) ≫
              DerivedCategory.Q.map
                ((NatTrans.mapHomologicalComplex adj₀.counit (.up ℤ)).app K))
    (ι : (Functor.curry.obj
        (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf)).obj
          (op ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              (SheafOfModules.unit Y.ringCatSheaf))) ≅ 𝟭 _)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
    ∃ d : L.obj (R.obj (DerivedCategory.Q.obj K)) ≅
        (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).obj
          (op ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))),
            DerivedCategory.Q.obj K),
    d.hom ≫ (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).map
        (((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map
            (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).op,
          𝟙 (DerivedCategory.Q.obj K)) ≫
        ι.hom.app (DerivedCategory.Q.obj K) = adj.counit.app (DerivedCategory.Q.obj K) := by
  have : IsGrothendieckAbelian.{u}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian _
  have hj₀ := affine_hom_kInjective_evaluation f H iH adj₀ h_eval
  let j := hj₀.choose
  have hj := hj₀.choose_spec
  let I := (CochainComplex.kInjectiveResolutionFunctor.{u}
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace))).obj K
  let s := (CochainComplex.toKInjectiveResolution.{u}
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace))).app K
  have : I.IsKInjective := inferInstance
  have : QuasiIso s :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ K).2
  have : IsIso (DerivedCategory.Q.map s) := inferInstance
  have : IsIso (β.app I) := comparison_isIso_on_kInjective H R β hR I
  let c := (hj I inferInstance).choose
  have hc := (hj I inferInstance).choose_spec
  let q : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj I :=
    asIso (DerivedCategory.Q.map s)
  let F := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
  let A := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))
  let O := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
      (SheafOfModules.unit Y.ringCatSheaf)
  let a : O ⟶ A := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
  let G := (Functor.curry.obj F).obj (op A)
  let U := (Functor.curry.obj F).obj (op O)
  let v : G ⟶ U := (Functor.curry.obj F).map a.op
  let dI : L.obj (R.obj (DerivedCategory.Q.obj I)) ≅ G.obj (DerivedCategory.Q.obj I) :=
    (L.mapIso (asIso (β.app I))).symm ≪≫
      t.app ((H.mapHomologicalComplex (.up ℤ)).obj I) ≪≫ c
  change c.hom ≫ v.app (DerivedCategory.Q.obj I) ≫
    j.hom.app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex adj₀.counit (.up ℤ)).app I) at hc
  have hdI : dI.hom ≫ v.app (DerivedCategory.Q.obj I) ≫
      j.hom.app (DerivedCategory.Q.obj I) = adj.counit.app (DerivedCategory.Q.obj I) := by
    dsimp only [dI, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, asIso_inv]
    simp only [Category.assoc]
    change L.map (inv (β.app I)) ≫
      t.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj I) ≫
        (c.hom ≫ _ ≫ _) = _
    rw [hc, ← h_counit I]
    rw [← L.map_comp_assoc, IsIso.inv_hom_id, L.map_id, Category.id_comp]
  have hd := transport_evaluation (R ⋙ L) G U adj.counit v j q dI hdI
  let d₀ := hd.choose
  have hd₀ := hd.choose_spec
  exact change_evaluation_iso G U v j ι d₀ (adj.counit.app _) hd₀

end AlgebraicGeometry
