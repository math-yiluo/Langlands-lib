/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.TorsionCompletionDefinitions
public import WeilConjectures.CategoryTheory.MultiplicationDifference
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import WeilConjectures.AlgebraicGeometry.LocalHomTowerCriterion
import all WeilConjectures.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.CategoryTheory.ScalarLocalizationRegularColimit
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts

set_option linter.privateModule false

/-! # The multiplication difference on a pro-etale slice

Source: Stacks Project, algebraization.tex, Tag 0997, and proetale.tex, Tag 099Q.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe t u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem module_equivalence
    {C D : Type*} [Category* C] [Category* D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (e : C ≌ D) [e.inverse.IsDenseSubsite K J]
    (R : Sheaf J RingCat.{w}) (S : Sheaf K RingCat.{w})
    (c : S ≅ (e.inverse.sheafPushforwardContinuous RingCat.{w} K J).obj R) :
    Nonempty (SheafOfModules.{w} R ≌ SheafOfModules.{w} S) := by
  let ψ : R ⟶ (e.functor.sheafPushforwardContinuous RingCat.{w} J K).obj S :=
    { hom := Functor.whiskerRight e.op.unitIso.hom R.obj ≫
        Functor.whiskerLeft e.functor.op c.inv.hom }
  have H₁ : Functor.whiskerRight (NatTrans.op e.symm.counit) R.obj =
      ψ.hom ≫ e.functor.op.whiskerLeft c.hom.hom := by
    apply NatTrans.ext
    funext U
    change R.obj.map _ =
      (R.obj.map _ ≫ c.inv.hom.app _) ≫ c.hom.hom.app _
    rw [Category.assoc]
    have hc := congrArg (fun f ↦ f.hom.app (e.functor.op.obj U)) c.inv_hom_id
    have hc' : c.inv.hom.app (e.functor.op.obj U) ≫
        c.hom.hom.app (e.functor.op.obj U) = 𝟙 _ := hc
    change R.obj.map (e.unitInv.app U.unop).op =
      R.obj.map (e.unitInv.app U.unop).op ≫
        (c.inv.hom.app (e.functor.op.obj U) ≫ c.hom.hom.app (e.functor.op.obj U))
    exact (Category.comp_id _).symm.trans
      (congrArg (fun f ↦ R.obj.map (e.unitInv.app U.unop).op ≫ f) hc'.symm)
  have H₂ : c.hom.hom ≫ e.inverse.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op e.symm.unit) S.obj = 𝟙 S.obj := by
    apply NatTrans.ext
    funext U
    change c.hom.hom.app U ≫
      (R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
        c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U))) ≫
        S.obj.map (e.counitInv.app U.unop).op = 𝟙 _
    rw [Category.assoc]
    have hn := c.inv.hom.naturality (e.counitInv.app U.unop).op
    change R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op ≫
      c.inv.hom.app U =
      c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U)) ≫
        S.obj.map (e.counitInv.app U.unop).op at hn
    rw [← hn]
    have hm : R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
        R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op = 𝟙 _ := by
      rw [← Functor.map_comp, ← op_comp]
      simp
    rw [← Category.assoc (R.obj.map _) (R.obj.map _) _, hm]
    change c.hom.hom.app U ≫ 𝟙 _ ≫ c.inv.hom.app U = 𝟙 _
    have hc : c.hom.hom.app U ≫ c.inv.hom.app U = 𝟙 _ :=
      congrArg (fun f ↦ f.hom.app U) c.hom_inv_id
    exact (congrArg (fun f ↦ c.hom.hom.app U ≫ f)
      (Category.id_comp (c.inv.hom.app U))).trans hc
  have : e.symm.functor.IsContinuous K J := inferInstanceAs (e.inverse.IsContinuous K J)
  have : e.symm.inverse.IsContinuous J K := inferInstanceAs (e.functor.IsContinuous J K)
  exact ⟨SheafOfModules.pushforwardPushforwardEquivalence e.symm c.hom ψ H₁ H₂⟩

private theorem slice_exact_products (X : Scheme.{t})
    (O : Sheaf (coefficientProEtaleModelTopology.{t, u} X)
      CommRingCat.{max u (t + 1)}) (U : coefficientProEtaleSiteModel.{t, u} X) :
    CountableAB4Star
      (SheafOfModules.{max u (t + 1)} ((localCoefficientRings O).over U)) := by
  let J := coefficientProEtaleModelTopology.{t, u} X
  let K := ProEt.topology X
  let d : coefficientProEtaleSiteModel.{t, u} X ≌ X.ProEt :=
    (AsSmall.equiv.{t, t + 1, max u (t + 1)} (C := X.ProEt)).symm
  let : (AsSmall.down : coefficientProEtaleSiteModel.{t, u} X ⥤ X.ProEt).IsEquivalence :=
    d.isEquivalence_functor
  have : d.functor.IsDenseSubsite J K := by
    change AsSmall.down.IsDenseSubsite (AsSmall.down.inducedTopology K) K
    infer_instance
  have : d.functor.IsCocontinuous J K := inferInstance
  have : d.inverse.IsCocontinuous K J := by
    apply (d.symm.toAdjunction.isCocontinuous_iff_coverPreserving K J).2
    exact Functor.IsDenseSubsite.coverPreserving J K d.functor
  let e₁ := Over.postEquiv (X := U) d
  have : e₁.functor.IsCocontinuous (J.over U) (K.over (d.functor.obj U)) :=
    inferInstanceAs ((Over.post d.functor).IsCocontinuous _ _)
  have : (Over.map (d.unitIso.inv.app U)).IsCocontinuous
      (J.over (d.inverse.obj (d.functor.obj U))) (J.over U) := by
    constructor
    intro V S hS
    change Sieve.overEquiv _ S ∈ J _ at hS
    change Sieve.overEquiv _ (S.functorPullback (Over.map (d.unitIso.inv.app U))) ∈ J _
    rwa [Sieve.overEquiv_functorPullback_map]
  have : e₁.inverse.IsCocontinuous (K.over (d.functor.obj U)) (J.over U) := by
    exact isCocontinuous_comp (Over.post d.inverse)
      (Over.map (d.unitIso.inv.app U)) (K.over (d.functor.obj U))
      (J.over (d.inverse.obj (d.functor.obj U)))
  have : e₁.inverse.IsDenseSubsite (K.over (d.functor.obj U)) (J.over U) :=
    e₁.isDenseSubsite_inverse_of_isCocontinuous _ _
  let W := d.functor.obj U
  let e₂ := ProEt.sliceEquiv X W
  have := ProEt.sliceDense X W
  let e := e₁.trans e₂
  let L := ProEt.topology W.left
  have : e.functor.IsCocontinuous (J.over U) L :=
    isCocontinuous_comp e₁.functor e₂.functor (J.over U) (K.over W)
  have : e.inverse.IsCocontinuous L (J.over U) :=
    isCocontinuous_comp e₂.inverse e₁.inverse L (K.over W)
  have : e.inverse.IsDenseSubsite L (J.over U) :=
    e.isDenseSubsite_inverse_of_isCocontinuous _ _
  let S := (e.inverse.sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
    L (J.over U)).obj (O.over U)
  obtain ⟨q⟩ := module_equivalence (J.over U) L e
    ((localCoefficientRings O).over U)
    ((sheafCompose L (forget₂ CommRingCat RingCat)).obj S) (Iso.refl _)
  let B := SheafOfModules.{max u (t + 1)}
    ((sheafCompose L (forget₂ CommRingCat RingCat)).obj S)
  let : CountableAB4Star B :=
    AlgebraicGeometry.ProEtale.exact_countable_products W.left S
  constructor
  intro I _
  exact HasExactLimitsOfShape.of_codomain_equivalence (Discrete I) q.symm

private theorem conjugate_isIso_iff
    {B : Type*} [Category* B] {M N : B} (e : M ≅ N)
    (a : M ⟶ M) (b : N ⟶ N) (h : a ≫ e.hom = e.hom ≫ b) :
    IsIso a ↔ IsIso b := by
  have hb : b = e.inv ≫ a ≫ e.hom := by rw [h]; simp
  have ha : a = e.hom ≫ b ≫ e.inv := by rw [← Category.assoc, ← h]; simp
  constructor
  · intro hi
    have := hi
    rw [hb]
    infer_instance
  · intro hi
    have := hi
    rw [ha]
    infer_instance

private theorem tower_map_iso_iff
    {B D : Type*} [Category* B] [Preadditive B] [Category* D] [Preadditive D]
    (P : B ⥤ D) [P.Additive]
    (K : ℕ → B) [HasProduct K] [HasProduct (fun n ↦ P.obj (K n))]
    [PreservesLimit (Discrete.functor K) P] (a : ∀ n, K (n + 1) ⟶ K n) :
    IsIso (P.map (towerTransitionEndomorphism a)) ↔
      IsIso (towerTransitionEndomorphism (K := fun n ↦ P.obj (K n))
        (fun n ↦ P.map (a n))) := by
  let e := PreservesProduct.iso P K
  apply conjugate_isIso_iff e
  apply Pi.hom_ext
  intro n
  dsimp only [e]
  simp only [Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π]
  rw [← P.map_comp, (towerTransitionEndomorphism_eq_iff a _).mp rfl n,
    P.map_sub, P.map_comp]
  simp [towerTransitionEndomorphism, towerProductShift]

private theorem complex_tower_isIso_of_components
    {B : Type*} [Category* B] [Abelian B] [HasCountableProducts B]
    (K : CochainComplex B ℤ) (a : K ⟶ K)
    (ha : ∀ i : ℤ, IsIso (towerTransitionEndomorphism
      (K := fun _ : ℕ ↦ K.X i) (fun _ ↦ a.f i))) :
    IsIso (towerTransitionEndomorphism (K := fun _ : ℕ ↦ K) (fun _ ↦ a)) := by
  have (i : ℤ) : IsIso
      ((towerTransitionEndomorphism (K := fun _ : ℕ ↦ K) (fun _ ↦ a)).f i) :=
    (tower_map_iso_iff (HomologicalComplex.eval B (.up ℤ) i)
      (fun _ : ℕ ↦ K) (fun _ ↦ a)).mpr (ha i)
  exact HomologicalComplex.Hom.isIso_of_components _

private theorem derived_tower_isIso_of_components
    {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    [HasCountableProducts B] [CountableAB4Star B]
    (K : CochainComplex B ℤ) (a : K ⟶ K)
    (ha : ∀ i : ℤ, IsIso (towerTransitionEndomorphism
      (K := fun _ : ℕ ↦ K.X i) (fun _ ↦ a.f i))) :
    let := (derivedCategory_countableProducts_core.{0} B).choose
    IsIso (towerTransitionEndomorphism
      (K := fun _ : ℕ ↦ DerivedCategory.Q.obj K) (fun _ ↦ DerivedCategory.Q.map a)) := by
  let := (derivedCategory_countableProducts_core.{0} B).choose
  have hP := (derivedCategory_countableProducts_core.{0} B).choose_spec.1 ℕ (fun _ ↦ K)
  let : PreservesLimit (Discrete.functor (fun _ : ℕ ↦ K)) DerivedCategory.Q :=
    preservesLimit_of_preserves_limit_cone (limit.isLimit _) hP.some
  have := complex_tower_isIso_of_components K a ha
  apply (tower_map_iso_iff DerivedCategory.Q (fun _ : ℕ ↦ K) (fun _ ↦ a)).mp
  infer_instance

private theorem towerIso_of_iso
    {B : Type*} [Category* B] [Preadditive B] [HasCountableProducts B]
    {M N : B} (e : M ≅ N) (a : M ⟶ M) (b : N ⟶ N)
    (h : a ≫ e.hom = e.hom ≫ b) :
    IsIso (towerTransitionEndomorphism (K := fun _ : ℕ ↦ M) (fun _ ↦ a)) ↔
      IsIso (towerTransitionEndomorphism (K := fun _ : ℕ ↦ N) (fun _ ↦ b)) := by
  apply conjugate_isIso_iff (Pi.mapIso (fun _ : ℕ ↦ e))
  exact (towerTransitionEndomorphism_natural_backward _ _ (fun _ ↦ e.hom)
    (fun _ ↦ h.symm)).symm

private theorem localHom_iff_towerIso
    {C : Type v} [SmallCategory C] (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{v}) (U : C) (f : O.obj.obj (op U))
    [HasDerivedCategory.{w} (ringedSiteModules.{v} (localCoefficientRings O))]
    [HasDerivedCategory.{w} (ringedSiteModules.{v} ((localCoefficientRings O).over U))]
    (K : DerivedCategory (ringedSiteModules.{v} (localCoefficientRings O)))
    [HasProduct (fun _ : ℕ ↦ (localCoefficientDerivedRestriction O U).obj K)] :
    IsZero ((derivedInternalHom (J.over U) (O.over U)).obj
      (op ((DerivedCategory.singleFunctor _ 0).obj (localCoefficientLocalization O U f)),
        (localCoefficientDerivedRestriction O U).obj K)) ↔
      IsIso (towerTransitionEndomorphism
        (K := fun _ : ℕ ↦ (localCoefficientDerivedRestriction O U).obj K)
        (fun _ ↦ (localSectionDerivedMultiplication O U f).app K)) := by
  obtain ⟨T, hT⟩ := (exists_isDerivedLimit_and_iso
    (fun _ : ℕ ↦ (localCoefficientDerivedRestriction O U).obj K)
    (fun _ ↦ (localSectionDerivedMultiplication O U f).app K)).1
  have h := localHom_zero_iff_multiplicationTower_zero J O U f K T hT
  obtain ⟨p, δ, hδ⟩ := hT
  exact h.trans (Pretriangulated.Triangle.isZero₁_iff_isIso₂
    (Pretriangulated.Triangle.mk p _ δ) hδ)

private theorem multiplication_fac
    {C : Type v} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{v}) (U : C) (f : O.obj.obj (op U))
    [HasDerivedCategory.{w} (ringedSiteModules.{v} (localCoefficientRings O))]
    [HasDerivedCategory.{w} (ringedSiteModules.{v} ((localCoefficientRings O).over U))]
    (K : CochainComplex (ringedSiteModules.{v} (localCoefficientRings O)) ℤ) :
    let := (localCoefficientRestriction_exact O U).1
    let := (localCoefficientRestriction_exact O U).2.1
    let := (localCoefficientRestriction_exact O U).2.2
    let T : ringedSiteModules.{v} (localCoefficientRings O) ⥤
        ringedSiteModules.{v} ((localCoefficientRings O).over U) :=
      SheafOfModules.overFunctor.{v} (localCoefficientRings O) U
    (localSectionDerivedMultiplication O U f).app (DerivedCategory.Q.obj K) ≫
        T.mapDerivedCategoryFactors.hom.app K =
      T.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (localSectionMultiplicationNatTrans O U f)
          (.up ℤ)).app K) := by
  have := (localCoefficientRestriction_exact O U).1
  have := (localCoefficientRestriction_exact O U).2.1
  have := (localCoefficientRestriction_exact O U).2.2
  dsimp only
  simp only [localSectionDerivedMultiplication, Localization.liftNatTrans_app,
    Category.assoc]
  let T : ringedSiteModules.{v} (localCoefficientRings O) ⥤
      ringedSiteModules.{v} ((localCoefficientRings O).over U) :=
    SheafOfModules.overFunctor.{v} (localCoefficientRings O) U
  change _ ≫ (_ ≫
    (T.mapDerivedCategoryFactors.inv.app K ≫ T.mapDerivedCategoryFactors.hom.app K)) = _
  rw [Iso.inv_hom_id_app, Category.comp_id]
  rfl

private theorem localHom_zero_of_termwise_difference
    {C : Type v} [SmallCategory C] (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{v}) (U : C) (f : O.obj.obj (op U))
    [HasDerivedCategory.{w} (ringedSiteModules.{v} (localCoefficientRings O))]
    [HasDerivedCategory.{w} (ringedSiteModules.{v} ((localCoefficientRings O).over U))]
    [CountableAB4Star (ringedSiteModules.{v} ((localCoefficientRings O).over U))]
    (K : CochainComplex (ringedSiteModules.{v} (localCoefficientRings O)) ℤ)
    (hK : ∀ i : ℤ, IsIso ((multiplicationDifference O U f).app ((K.X i).over U))) :
    IsZero ((derivedInternalHom (J.over U) (O.over U)).obj
      (op ((DerivedCategory.singleFunctor _ 0).obj (localCoefficientLocalization O U f)),
        (localCoefficientDerivedRestriction O U).obj (DerivedCategory.Q.obj K))) := by
  let B := ringedSiteModules.{v} ((localCoefficientRings O).over U)
  let := (derivedCategory_countableProducts_core.{0} B).choose
  have := (localCoefficientRestriction_exact O U).1
  have := (localCoefficientRestriction_exact O U).2.1
  have := (localCoefficientRestriction_exact O U).2.2
  apply (localHom_iff_towerIso J O U f _).mpr
  let T : ringedSiteModules.{v} (localCoefficientRings O) ⥤
      ringedSiteModules.{v} ((localCoefficientRings O).over U) :=
    SheafOfModules.overFunctor.{v} (localCoefficientRings O) U
  let L := (T.mapHomologicalComplex (.up ℤ)).obj K
  let a := (NatTrans.mapHomologicalComplex
    (localSectionMultiplicationNatTrans O U f) (.up ℤ)).app K
  apply (towerIso_of_iso (T.mapDerivedCategoryFactors.app K) _
    (DerivedCategory.Q.map a) (multiplication_fac O U f K)).mpr
  exact derived_tower_isIso_of_components L a hK

private theorem coefficientLocalizationIso
    {C : Type v} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{v}) (U : C) (f : O.obj.obj (op U)) :
    Nonempty (localCoefficientLocalization O U f ≅
      ringedSectionLocalization (O.over U) (ringedSliceSection O U f)) := by
  have hm : localSectionMultiplication O U f (SheafOfModules.unit _) =
      (SheafOfModules.unitHomEquiv _).symm
        ⟨(ringedSliceSection O U f).val, (ringedSliceSection O U f).property⟩ := by
    apply (SheafOfModules.forget _).map_injective
    apply PresheafOfModules.Hom.ext
    funext V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change O.obj.obj (op V.unop.left) at x
    change O.obj.map V.unop.hom.op f * x = x * O.obj.map V.unop.hom.op f
    exact mul_comm _ _
  obtain ⟨c, ⟨hc⟩, e, _⟩ :=
    scalarLocalization_regularColimit (O.over U) (ringedSliceSection O U f)
  unfold localCoefficientLocalization
  simp_rw [hm]
  exact ⟨colimit.isoColimitCocone ⟨c, hc⟩ ≪≫ e⟩

end AlgebraicGeometry.Scheme
