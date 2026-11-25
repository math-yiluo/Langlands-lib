/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantCohomology
public import WeilConjectures.RingTheory.DerivedModuleScalarAdjunction
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantScalarExtension
import all WeilConjectures.CategoryTheory.ConstantScalarRealization.ConstantRealizationDerivedScalarExtensionSupplement
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientLiftKFlatResolution

/-! # Formula for the canonical transpose of the lifted transition

Source: Stacks Project, Tags 06YY and 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-lifted-transition-canonical-transpose-formula).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived

attribute [local instance] finitePerfectModelsAbLocallyBijective

attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  HasDerivedCategory.standard

/-- The mate of the lifted unit, using the exact restriction comparison. -/
private def liftScalarMate {B D : Type t} [CommRing B] [CommRing D]
    (q : B →+* D) (P : DerivedCategory (ModuleCat.{t} B)) :
    (ConstantScalarRealization.moduleDerivedExtension (RingHom.ulift.{t + 1, t + 1} q)).obj
        ((finitePerfectAdicAlgebraLift B).obj P) ⟶
      (finitePerfectAdicAlgebraLift D).obj
        ((ConstantScalarRealization.moduleDerivedExtension q).obj P) :=
  ((ConstantScalarRealization.moduleDerivedAdjunction
    (RingHom.ulift.{t + 1, t + 1} q)).homEquiv _ _).symm
      ((finitePerfectAdicAlgebraLift B).map
        ((ConstantScalarRealization.moduleDerivedAdjunction q).unit.app P) ≫
      (finitePerfectAdicAlgebraLiftRestrict q).inv.app
        ((ConstantScalarRealization.moduleDerivedExtension q).obj P))

private theorem liftScalarMate_homEquiv {B D : Type t} [CommRing B] [CommRing D]
    (q : B →+* D) (P : DerivedCategory (ModuleCat.{t} B)) :
    (ConstantScalarRealization.moduleDerivedAdjunction
      (RingHom.ulift.{t + 1, t + 1} q)).homEquiv
        ((finitePerfectAdicAlgebraLift B).obj P) _ (liftScalarMate q P) =
      (finitePerfectAdicAlgebraLift B).map
        ((ConstantScalarRealization.moduleDerivedAdjunction q).unit.app P) ≫
        (finitePerfectAdicAlgebraLiftRestrict q).inv.app
          ((ConstantScalarRealization.moduleDerivedExtension q).obj P) := by
  exact Equiv.apply_symm_apply _ _

private theorem liftScalarMate_naturality {B D : Type t} [CommRing B] [CommRing D]
    (q : B →+* D) {P K : DerivedCategory (ModuleCat.{t} B)} (f : P ⟶ K) :
    (ConstantScalarRealization.moduleDerivedExtension (RingHom.ulift.{t + 1, t + 1} q)).map
        ((finitePerfectAdicAlgebraLift B).map f) ≫ liftScalarMate q K =
      liftScalarMate q P ≫ (finitePerfectAdicAlgebraLift D).map
        ((ConstantScalarRealization.moduleDerivedExtension q).map f) := by
  apply ((ConstantScalarRealization.moduleDerivedAdjunction
    (RingHom.ulift.{t + 1, t + 1} q)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [liftScalarMate, Equiv.apply_symm_apply]
  rw [← Category.assoc, ← Functor.map_comp]
  rw [← (ConstantScalarRealization.moduleDerivedAdjunction q).unit_naturality]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  congr 1
  exact (finitePerfectAdicAlgebraLiftRestrict q).inv.naturality
    ((ConstantScalarRealization.moduleDerivedExtension q).map f)

attribute [local irreducible] ConstantScalarRealization.moduleDerivedExtension
  ConstantScalarRealization.moduleDerivedAdjunction

/-- Compatibility of the mate with the ordinary tensor comparison on representatives. -/
private theorem liftScalarMate_representative_square
    {B D : Type t} [CommRing B] [CommRing D]
    (q : B →+* D) (P : CochainComplex (ModuleCat.{t} B) ℤ) :
    liftScalarMate q (DerivedCategory.Q.obj P) ≫
        (finitePerfectAdicAlgebraLift D).map
          (ConstantScalarRealization.moduleRepresentative q P) ≫
        (coefficientLift D).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars q).mapHomologicalComplex (.up ℤ)).obj P) =
      (ConstantScalarRealization.moduleDerivedExtension (RingHom.ulift.{t + 1, t + 1} q)).map
          ((coefficientLift B).mapDerivedCategoryFactors.hom.app P) ≫
        ConstantScalarRealization.moduleRepresentative (RingHom.ulift.{t + 1, t + 1} q)
          (((coefficientLift B).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso
            (liftedTensorComparison q) (.up ℤ)).inv.app P) := by
  let cR := coefficientLift B
  let cS := coefficientLift D
  let cr := finitePerfectAdicAlgebraLift B
  let cs := finitePerfectAdicAlgebraLift D
  let U := ModuleCat.restrictScalars (RingHom.ulift.{t + 1, t + 1} q)
  let Um := ModuleCat.restrictScalars q
  let ur := U.mapDerivedCategory
  let um := Um.mapDerivedCategory
  let ad := ConstantScalarRealization.moduleDerivedAdjunction
    (RingHom.ulift.{t + 1, t + 1} q)
  let md := ConstantScalarRealization.moduleDerivedAdjunction q
  let Q := DerivedCategory.Q (C := ModuleCat.{t + 1} (ULift.{t + 1} B))
  let E := ModuleCat.extendScalars q
  let P' := (E.mapHomologicalComplex (.up ℤ)).obj P
  let cP := (cR.mapHomologicalComplex (.up ℤ)).obj P
  let e := finitePerfectAdicAlgebraLiftRestrict q
  let e₀ : Um ⋙ cR ≅ cS ⋙ U := NatIso.ofComponents (fun _ ↦ Iso.refl _)
  let γ := (NatTrans.mapHomologicalComplex e₀.hom (.up ℤ)).app P'
  let κ := (Functor.mapHomologicalComplexCompIso
    (liftedTensorComparison q) (.up ℤ)).inv.app P
  have hm : md.unit.app (DerivedCategory.Q.obj P) ≫
      um.map (ConstantScalarRealization.moduleRepresentative q P) =
    DerivedCategory.Q.map
      (((ModuleCat.extendRestrictScalarsAdj q).mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        Um.mapDerivedCategoryFactors.inv.app P' := by
    exact (md.homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  have hs : ad.unit.app (Q.obj cP) ≫
      ur.map (ConstantScalarRealization.moduleRepresentative
        (RingHom.ulift.{t + 1, t + 1} q) cP) =
    Q.map (((ModuleCat.extendRestrictScalarsAdj.{t + 1, t + 1, t + 1}
      (RingHom.ulift.{t + 1, t + 1} q)).mapHomologicalComplex (.up ℤ)).unit.app cP) ≫
      U.mapDerivedCategoryFactors.inv.app
        (((ModuleCat.extendScalars.{t + 1, t + 1, t + 1}
          (RingHom.ulift.{t + 1, t + 1} q)).mapHomologicalComplex (.up ℤ)).obj cP) := by
    exact (ad.homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  have hc : ((ModuleCat.extendRestrictScalarsAdj.{t + 1, t + 1, t + 1}
        (RingHom.ulift.{t + 1, t + 1} q)).mapHomologicalComplex (.up ℤ)).unit.app cP ≫
      (U.mapHomologicalComplex (.up ℤ)).map κ =
    (cR.mapHomologicalComplex (.up ℤ)).map
      (((ModuleCat.extendRestrictScalarsAdj q).mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        γ := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rcases x with ⟨x⟩
    rfl
  have he := Functor.exactSquare_fac e₀ P'
  change e.inv.app (DerivedCategory.Q.obj P') ≫
      ur.map (cS.mapDerivedCategoryFactors.hom.app P') ≫
      U.mapDerivedCategoryFactors.hom.app ((cS.mapHomologicalComplex (.up ℤ)).obj P') =
    cr.map (Um.mapDerivedCategoryFactors.hom.app P') ≫
      cR.mapDerivedCategoryFactors.hom.app ((Um.mapHomologicalComplex (.up ℤ)).obj P') ≫
        Q.map γ at he
  apply ad.homEquiv _ _ |>.injective
  rw [Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  dsimp only [ad]
  rw [liftScalarMate_homEquiv q (DerivedCategory.Q.obj P)]
  simp only [Category.assoc]
  apply (cancel_mono (U.mapDerivedCategoryFactors.hom.app
    ((cS.mapHomologicalComplex (.up ℤ)).obj P'))).mp
  rw [Adjunction.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  have hn := e.inv.naturality (ConstantScalarRealization.moduleRepresentative q P)
  change cr.map (um.map (ConstantScalarRealization.moduleRepresentative q P)) ≫
      e.inv.app (DerivedCategory.Q.obj P') =
    e.inv.app _ ≫ ur.map (cs.map (ConstantScalarRealization.moduleRepresentative q P)) at hn
  dsimp only [cr, cs, finitePerfectAdicAlgebraLift] at he hn ⊢
  rw [← reassoc_of% hn, ← Functor.map_comp_assoc, hm]
  simp only [Functor.map_comp, Category.assoc]
  rw [he]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  have hnat := cR.mapDerivedCategoryFactors.hom.naturality
    (((ModuleCat.extendRestrictScalarsAdj q).mapHomologicalComplex (.up ℤ)).unit.app P)
  change cr.map (DerivedCategory.Q.map _) ≫ cR.mapDerivedCategoryFactors.hom.app _ =
    cR.mapDerivedCategoryFactors.hom.app P ≫ Q.map _ at hnat
  dsimp only [cr, finitePerfectAdicAlgebraLift] at hnat
  rw [reassoc_of% hnat, ← Q.map_comp, ← hc]
  rw [Functor.map_comp]
  have hu := U.mapDerivedCategoryFactors.hom.naturality κ
  change ur.map (DerivedCategory.Q.map κ) ≫ U.mapDerivedCategoryFactors.hom.app _ =
    U.mapDerivedCategoryFactors.hom.app _ ≫
      Q.map ((U.mapHomologicalComplex (.up ℤ)).map κ) at hu
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hs]
  erw [hu]
  erw [Iso.inv_hom_id_app_assoc]

/-- A resolution that stays K-flat after coefficient lift makes the mate invertible. -/
private theorem liftScalarMate_isIso {B D : Type t} [CommRing B] [CommRing D]
    (q : B →+* D) (M : DerivedCategory (ModuleCat.{t} B)) : IsIso (liftScalarMate q M) := by
  let P := DerivedCategory.Q.objPreimage M
  obtain ⟨K, f, hf, hK, hK'⟩ := P.exists_coefficientLift_kFlat_resolution
  have : QuasiIso f := hf
  have : IsIso (ConstantScalarRealization.moduleRepresentative q K) :=
    ConstantScalarRealization.moduleRepresentative_isIso q K hK
  have : IsIso (ConstantScalarRealization.moduleRepresentative
      (RingHom.ulift.{t + 1, t + 1} q)
      (((coefficientLift B).mapHomologicalComplex (.up ℤ)).obj K)) :=
    ConstantScalarRealization.moduleRepresentative_isIso _ _ hK'
  have hs := liftScalarMate_representative_square q K
  have : IsIso (liftScalarMate q (DerivedCategory.Q.obj K)) := by
    have : IsIso (liftScalarMate q (DerivedCategory.Q.obj K) ≫
        ((finitePerfectAdicAlgebraLift D).map
          (ConstantScalarRealization.moduleRepresentative q K) ≫
          (coefficientLift D).mapDerivedCategoryFactors.hom.app
            (((ModuleCat.extendScalars q).mapHomologicalComplex (.up ℤ)).obj K))) := by
      rw [hs]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((finitePerfectAdicAlgebraLift D).map
        (ConstantScalarRealization.moduleRepresentative q K) ≫
        (coefficientLift D).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars q).mapHomologicalComplex (.up ℤ)).obj K))
  let e : DerivedCategory.Q.obj K ≅ M :=
    asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso M
  have hn := liftScalarMate_naturality q e.hom
  exact IsIso.of_isIso_fac_left hn

attribute [local semireducible] ConstantScalarRealization.moduleDerivedExtension
  ConstantScalarRealization.moduleDerivedAdjunction

/-- The canonical transpose is the lifted supplied transpose, up to a comparison iso.
The canonical unit mate is invertible by its representative square and a resolution that
remains K-flat after coefficient lift. Compose it with the lift of `leftAdjointUniq` for the
supplied step adjunction. Naturality of `finitePerfectAdicAlgebraLiftRestrict` and the unit
identity for `leftAdjointUniq` then give the displayed transpose formula.
(blueprint: lem-weil-pbc-finite-perfect-adic-lifted-transition-canonical-transpose-formula). -/
theorem finitePerfectAdicLiftedTransition_canonical_transpose_formula
    {A : Type t} [CommRing A] {d : AdicCoefficientDatum A}
    (T : FinitePerfectAdicAlgebraTower d) (n : ℕ) :
    let q : ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1)) →+*
        ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)) :=
      RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1))
    letI : (normalizationModuleRestrict q).IsRightAdjoint :=
      ModuleCat.derivedRestrictScalars_isRightAdjoint.{t + 1, 0} q
    let adj := Adjunction.ofIsRightAdjoint (normalizationModuleRestrict q)
    ∃ e : (normalizationModuleRestrict q).leftAdjoint.obj
          ((finitePerfectAdicAlgebraLift _).obj (T.level (n + 1))) ≅
        (finitePerfectAdicAlgebraLift _).obj
          ((T.stepExtension n).obj (T.level (n + 1))),
      (adj.homEquiv _ _).symm (finitePerfectAdicLiftedTransition T n) =
        e.hom ≫ (finitePerfectAdicAlgebraLift _).map
          ((T.stepAdjunction n).homEquiv _ _ |>.symm (T.transition n)) := by
  let q₀ := Ideal.Quotient.factorPowSucc d.ideal (n + 1)
  let q := RingHom.ulift.{t + 1, t + 1} q₀
  let md := ConstantScalarRealization.moduleDerivedAdjunction q₀
  let ad := ConstantScalarRealization.moduleDerivedAdjunction q
  let c := md.leftAdjointUniq (T.stepAdjunction n)
  have : IsIso (liftScalarMate q₀ (T.level (n + 1))) :=
    liftScalarMate_isIso q₀ _
  refine ⟨asIso (liftScalarMate q₀ (T.level (n + 1))) ≪≫
    (finitePerfectAdicAlgebraLift _).mapIso (c.app (T.level (n + 1))), ?_⟩
  change (ad.homEquiv _ _).symm (finitePerfectAdicLiftedTransition T n) = _
  apply (ad.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  simp only [Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Category.assoc]
  rw [Adjunction.homEquiv_naturality_right]
  dsimp only [ad, q]
  rw [liftScalarMate_homEquiv q₀ (T.level (n + 1))]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (finitePerfectAdicAlgebraLiftRestrict q₀).inv.naturality
    (c.app (T.level (n + 1))).hom
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn, ← Functor.map_comp_assoc]
  have hc := md.unit_leftAdjointUniq_hom_app (T.stepAdjunction n) (T.level (n + 1))
  change (ConstantScalarRealization.moduleDerivedAdjunction q₀).unit.app
      (T.level (n + 1)) ≫
    (ModuleCat.restrictScalars q₀).mapDerivedCategory.map (c.app (T.level (n + 1))).hom =
      (T.stepAdjunction n).unit.app (T.level (n + 1)) at hc
  rw [hc]
  have hn' := (finitePerfectAdicAlgebraLiftRestrict q₀).inv.naturality
    (((T.stepAdjunction n).homEquiv _ _).symm (T.transition n))
  dsimp only [Functor.comp_map] at hn'
  rw [← hn', ← Functor.map_comp_assoc]
  have ht : (T.stepAdjunction n).unit.app (T.level (n + 1)) ≫
      (ModuleCat.restrictScalars q₀).mapDerivedCategory.map
        (((T.stepAdjunction n).homEquiv _ _).symm (T.transition n)) = T.transition n := by
    exact ((T.stepAdjunction n).homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  rw [ht]
  rfl

end AlgebraicGeometry.Scheme
