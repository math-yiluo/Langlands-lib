/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import
  WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.DerivabilityStructureKInjectives
import Mathlib.RingTheory.Nilpotent.Basic
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit

/-! # Derived orthogonality of finite-torsion tower limits

The countable-power difference operator gives completeness directly.
(blueprint: lem-sfb-finite-tower-limit-orthogonality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe a b v w
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace CategoryTheory

private abbrev sequencePower
    (A : Type*) [Category* A] [HasCountableProducts A] : A ⥤ A where
  obj M := ∏ᶜ fun _ : ℕ ↦ M
  map f := Limits.Pi.map fun _ ↦ f
  map_id M := by ext n; simp
  map_comp f g := by ext n; simp

private noncomputable instance sequencePower_preservesLimits
    {A : Type*} [Category* A] [HasCountableProducts A]
    {D : Type*} [Category* D] : PreservesLimitsOfShape D (sequencePower A) := by
  let T := (Functor.const (Discrete ℕ) : A ⥤ (Discrete ℕ ⥤ A)) ⋙ lim
  let e : sequencePower A ≅ T :=
    NatIso.ofComponents (fun M ↦ Pi.isoLimit ((Functor.const (Discrete ℕ)).obj M)) (by
      intro M N f
      apply limit.hom_ext
      rintro ⟨n⟩
      simp [sequencePower, T])
  exact preservesLimitsOfShape_of_natIso e.symm

private def sequenceDifference
    (A : Type*) [Category* A] [Preadditive A] [HasCountableProducts A]
    (l : ℕ) : sequencePower A ⟶ sequencePower A where
  app M := 𝟙 _ - l • Pi.lift (fun n : ℕ ↦ Pi.π (fun _ : ℕ ↦ M) (n + 1))
  naturality {M N} f := by
    apply Pi.hom_ext
    intro n
    simp [sequencePower, Preadditive.comp_sub, Preadditive.sub_comp]

private theorem sequenceDifference_projection
    {A : Type*} [Category* A] [Preadditive A] [HasCountableProducts A]
    (l : ℕ) (M : A) (n : ℕ) :
    (sequenceDifference A l).app M ≫ Pi.π (fun _ : ℕ ↦ M) n =
      Pi.π (fun _ : ℕ ↦ M) n - l • Pi.π (fun _ : ℕ ↦ M) (n + 1) := by
  dsimp only [sequenceDifference, sequencePower]
  rw [Preadditive.sub_comp, Category.id_comp, Preadditive.nsmul_comp, Pi.lift_comp_π]

private theorem sequenceDifference_map
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    [HasCountableProducts A] [HasCountableProducts B] (F : A ⥤ B) [F.Additive]
    (l : ℕ) (M : A) :
    F.map ((sequenceDifference A l).app M) ≫ piComparison F (fun _ : ℕ ↦ M) =
      piComparison F (fun _ : ℕ ↦ M) ≫ (sequenceDifference B l).app (F.obj M) := by
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, piComparison_comp_π]
  rw [← F.map_comp, sequenceDifference_projection, F.map_sub, F.map_nsmul]
  rw [sequenceDifference_projection, Preadditive.comp_sub, Preadditive.comp_nsmul,
    piComparison_comp_π, piComparison_comp_π]

private theorem sequenceDifference_map_isIso_iff
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    [HasCountableProducts A] [HasCountableProducts B] (F : A ⥤ B) [F.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) F] (l : ℕ) (M : A) :
    IsIso (F.map ((sequenceDifference A l).app M)) ↔
      IsIso ((sequenceDifference B l).app (F.obj M)) := by
  have h := sequenceDifference_map F l M
  constructor
  · intro hF
    have := hF
    apply (isIso_comp_left_iff (piComparison F (fun _ : ℕ ↦ M)) _).mp
    rw [← h]
    infer_instance
  · intro hM
    have := hM
    apply (isIso_comp_right_iff _ (piComparison F (fun _ : ℕ ↦ M))).mp
    rw [h]
    infer_instance

private theorem sequenceDifference_iso
    {A : Type*} [Category* A] [Preadditive A] [HasCountableProducts A]
    (l : ℕ) {M N : A} (e : M ≅ N)
    (hN : IsIso ((sequenceDifference A l).app N)) :
    IsIso ((sequenceDifference A l).app M) := by
  have := hN
  have h : (sequenceDifference A l).app M =
      (sequencePower A).map e.hom ≫ (sequenceDifference A l).app N ≫
        (sequencePower A).map e.inv := by
    rw [← Category.assoc, (sequenceDifference A l).naturality,
      Category.assoc, ← Functor.map_comp, e.hom_inv_id, (sequencePower A).map_id, Category.comp_id]
  rw [h]
  infer_instance

private theorem sequenceDifference_limit
    {A : Type*} [Category* A] [Preadditive A] [HasCountableProducts A]
    {D : Type*} [Category* D] (F : D ⥤ A) [HasLimit F]
    [PreservesLimit F (sequencePower A)] (l : ℕ)
    (hF : ∀ d, IsIso ((sequenceDifference A l).app (F.obj d))) :
    IsIso ((sequenceDifference A l).app (limit F)) := by
  let δ := sequenceDifference A l
  let P := sequencePower A
  let α := Functor.whiskerLeft F δ
  have (d : D) : IsIso (α.app d) := hF d
  have : IsIso α := NatIso.isIso_of_isIso_app α
  let hc := isLimitOfPreserves P (limit.isLimit F)
  let e := IsLimit.conePointsIsoOfNatIso hc hc (asIso α)
  have he : δ.app (limit F) = e.hom := by
    apply hc.hom_ext
    intro d
    change δ.app (limit F) ≫ P.map (limit.π F d) = _
    rw [← δ.naturality]
    exact (IsLimit.conePointsIsoOfNatIso_hom_comp hc hc (asIso α) d).symm
  rw [he]
  infer_instance

private theorem sequenceDifference_nilpotent
    {A : Type*} [Category* A] [Preadditive A] [HasCountableProducts A]
    (l : ℕ) (M : A) (e : ℕ) (he : l ^ e • 𝟙 M = 0) :
    IsIso ((sequenceDifference A l).app M) := by
  let s : End (∏ᶜ fun _ : ℕ ↦ M) :=
    .of (l • Pi.lift (fun n : ℕ ↦ Pi.π (fun _ : ℕ ↦ M) (n + 1)))
  have hs (r j : ℕ) : ((s ^ r).asHom) ≫ Pi.π (fun _ : ℕ ↦ M) j =
      l ^ r • Pi.π (fun _ : ℕ ↦ M) (j + r) := by
    induction r generalizing j with
    | zero => simp
    | succ r ih =>
      rw [pow_succ, End.mul_asHom, Category.assoc, ih]
      simp only [s, Preadditive.nsmul_comp, Preadditive.comp_nsmul, Pi.lift_comp_π]
      rw [smul_smul, ← pow_succ]
      simp only [Nat.add_assoc]
  have hnil : IsNilpotent s := by
    refine ⟨e, End.ext (Pi.hom_ext _ _ fun j ↦ ?_)⟩
    rw [hs, ← Category.comp_id (Pi.π (fun _ : ℕ ↦ M) (j + e)),
      ← Preadditive.comp_nsmul, he, comp_zero, End.zero_asHom, zero_comp]
  exact (isUnit_iff_isIso (1 - s)).mp hnil.isUnit_one_sub

private theorem sequenceDifference_orthogonal
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    [HasCountableProducts A] (F : A ⥤ B) [F.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) F] (l : ℕ) (M : A)
    (hM : IsIso ((sequenceDifference A l).app M)) (V : B)
    [IsIso (l • 𝟙 V)] : Subsingleton (V ⟶ F.obj M) := by
  let g (f : V ⟶ F.obj M) : ℕ → (V ⟶ F.obj M) :=
    Nat.rec f (fun _ a ↦ inv (l • 𝟙 V) ≫ a)
  have hg (f : V ⟶ F.obj M) (n : ℕ) : l • g f (n + 1) = g f n := by
    change l • (inv (l • 𝟙 V) ≫ g f n) = _
    calc
      l • (inv (l • 𝟙 V) ≫ g f n) =
          (l • 𝟙 V) ≫ inv (l • 𝟙 V) ≫ g f n := by
        simp only [Preadditive.nsmul_comp, Category.id_comp]
      _ = g f n := IsIso.hom_inv_id_assoc _ _
  let P := Fan.mk (F.obj (∏ᶜ fun _ : ℕ ↦ M))
    (fun n : ℕ ↦ F.map (Pi.π (fun _ : ℕ ↦ M) n))
  have hP : IsLimit P :=
    (isLimitMapConeFanMkEquiv F _ _) (isLimitOfPreserves F (productIsProduct _))
  have hz (f : V ⟶ F.obj M) : f = 0 := by
    let a := Fan.IsLimit.lift hP (g f)
    have ha_proj (n : ℕ) : a ≫ F.map (Pi.π (fun _ : ℕ ↦ M) n) = g f n :=
      Fan.IsLimit.fac hP (g f) n
    have ha : a ≫ F.map ((sequenceDifference A l).app M) = 0 := by
      apply Fan.IsLimit.hom_ext hP
      intro n
      change (a ≫ F.map ((sequenceDifference A l).app M)) ≫
        F.map (Pi.π (fun _ : ℕ ↦ M) n) =
          (0 : V ⟶ F.obj (∏ᶜ fun _ : ℕ ↦ M)) ≫ F.map (Pi.π (fun _ : ℕ ↦ M) n)
      rw [Category.assoc, ← F.map_comp, sequenceDifference_projection,
        F.map_sub, F.map_nsmul, Preadditive.comp_sub, Preadditive.comp_nsmul]
      simp only [ha_proj, hg, sub_self, zero_comp]
    have : IsIso (F.map ((sequenceDifference A l).app M)) := by
      have := hM
      infer_instance
    have ha0 : a = 0 := (cancel_mono (F.map ((sequenceDifference A l).app M))).mp
      (by simpa only [zero_comp] using ha)
    have hh := Fan.IsLimit.fac hP (g f) 0
    change a ≫ F.map (Pi.π _ 0) = f at hh
    rw [ha0, zero_comp] at hh
    exact hh.symm
  exact ⟨fun f h ↦ (hz f).trans (hz h).symm⟩

private theorem single_preserves_products
    (A : Type a) [Category.{v} A] [Abelian A] [HasCountableProducts A]
    [HasExactLimitsOfShape (Discrete ℕ) A] [HasDerivedCategory.{w} A]
    [Abelian.HasKInjectiveResolutions A] :
    PreservesLimitsOfShape (Discrete ℕ) (DerivedCategory.singleFunctor A 0) := by
  have : PreservesLimitsOfShape (Discrete ℕ) ((CochainComplex.singleFunctors A).functor 0) :=
    inferInstanceAs (PreservesLimitsOfShape _ (HomologicalComplex.single A (.up ℤ) 0))
  exact preservesLimitsOfShape_of_natIso (DerivedCategory.singleFunctorIsoCompQ A 0).symm

private theorem tower_limit_difference
    {A : Type a} [Category.{v} A] [Preadditive A] [HasCountableProducts A]
    [HasLimitsOfShape ℕᵒᵖ A] (l : ℕ) (H : ℕᵒᵖ ⥤ A)
    (hH : ∀ n : ℕ, l ^ (n + 1) • 𝟙 (H.obj (op n)) = 0) :
    IsIso ((sequenceDifference A l).app (limit H)) :=
  sequenceDifference_limit H l
    (fun n ↦ sequenceDifference_nilpotent l (H.obj n) (n.unop + 1) (hH n.unop))

private theorem complete_of_difference
    {A : Type a} [Category.{v} A] [Abelian A] [HasCountableProducts A]
    [HasExactLimitsOfShape (Discrete ℕ) A] [HasDerivedCategory.{w} A]
    [Abelian.HasKInjectiveResolutions A] (l : ℕ) (M : A)
    (hM : IsIso ((sequenceDifference A l).app M)) :
    ∀ V : DerivedCategory A, IsIso (l • 𝟙 V) →
      Subsingleton (V ⟶ (DerivedCategory.singleFunctor A 0).obj M) := by
  have := single_preserves_products A
  intro V hV
  have := hV
  exact sequenceDifference_orthogonal (DerivedCategory.singleFunctor A 0) l M hM V

private theorem orthogonal_iso
    {C : Type a} [Category.{v} C] [Preadditive C] (l : ℕ) {M N : C} (e : M ≅ N)
    (hN : ∀ V : C, IsIso (l • 𝟙 V) → Subsingleton (V ⟶ N)) :
    ∀ V : C, IsIso (l • 𝟙 V) → Subsingleton (V ⟶ M) := by
  intro V hV
  exact ⟨fun f g ↦ (cancel_mono e.hom).mp ((hN V hV).elim (f ≫ e.hom) (g ≫ e.hom))⟩

private theorem orthogonal_shift
    {C : Type a} [Category.{v} C] [Preadditive C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] (l : ℕ) (M : C)
    (hM : ∀ V : C, IsIso (l • 𝟙 V) → Subsingleton (V ⟶ M)) (n : ℤ) :
    ∀ V : C, IsIso (l • 𝟙 V) → Subsingleton (V ⟶ M⟦n⟧) := by
  let E := shiftEquiv C n
  have : E.inverse.Additive := by
    dsimp only [E, shiftEquiv, shiftEquiv']
    infer_instance
  intro V hV
  have : IsIso (l • 𝟙 (E.inverse.obj V)) := by
    have := hV
    rw [← E.inverse.map_id, ← E.inverse.map_nsmul]
    infer_instance
  have hs := hM (E.inverse.obj V) inferInstance
  refine ⟨fun f g ↦ ?_⟩
  apply (cancel_epi (E.counitIso.app V).hom).mp
  let ff := E.fullyFaithfulFunctor
  exact (ff.map_preimage ((E.counitIso.app V).hom ≫ f)).symm.trans
    ((congrArg E.functor.map (hs.elim
      (ff.preimage ((E.counitIso.app V).hom ≫ f))
      (ff.preimage ((E.counitIso.app V).hom ≫ g)))).trans (ff.map_preimage _))

attribute [local irreducible] DerivedCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ HasDerivedCategory.standard
  HomotopyCategory.singleFunctors Functor.mapDerivedCategory
  Functor.mapDerivedCategorySingleFunctor

/-- Finite-torsion tower limits are orthogonal to objects on which the scalar is invertible,
both before and after exact, product-preserving, conservative scalar restriction.

Source: the completeness step of the diagonal tower limit proof, paragraphs (1) and (3),
and the countable-product telescope argument of Stacks 099L/099M.
(blueprint: lem-sfb-finite-tower-limit-orthogonality).

Proof: on a countable power use the difference operator 1 minus l times the shift.
For an object killed by a power of l this operator has a finite geometric inverse.
Countable powers preserve limits, so the operator is invertible on each displayed
tower limit. Product preservation and conservativity reflect this property to P and Q.
Exact countable products and K-injective resolutions make the single-complex functor
preserve products. Any map from an l-invertible object can then be divided successively
by l, producing an element of the kernel of this invertible difference operator;
its zeroth component is the original map, hence is zero. Shift equivalences preserve
this orthogonality. The canonical single-complex and shift comparisons give the two
assertions after derived scalar restriction. No epimorphic-transition assumption is needed.
-/
theorem finite_tower_limit_orthogonality
    {A : Type a} [Category.{v} A] [Abelian A] [HasCountableProducts A]
    [HasExactLimitsOfShape (Discrete ℕ) A] [HasDerivedCategory.{w} A]
    [Abelian.HasKInjectiveResolutions A]
    {B : Type b} [Category B] [Abelian B] [HasCountableProducts B]
    [HasLimitsOfShape ℕᵒᵖ B] [HasExactLimitsOfShape (Discrete ℕ) B]
    [HasDerivedCategory.{w} B] [Abelian.HasKInjectiveResolutions B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesLimitsOfShape (Discrete ℕ) F] [F.ReflectsIsomorphisms]
    (l : ℕ) (n : ℤ) (P Q : A) (S H : ℕᵒᵖ ⥤ B)
    (s : F.obj P ≅ limit S) (t : F.obj Q ≅ limit H)
    (hS : ∀ n : ℕ, l ^ (n + 1) • 𝟙 (S.obj (op n)) = 0)
    (hH : ∀ n : ℕ, l ^ (n + 1) • 𝟙 (H.obj (op n)) = 0) :
    (∀ V : DerivedCategory A, IsIso (l • 𝟙 V) →
      Subsingleton (V ⟶ (DerivedCategory.singleFunctor A 0).obj P)) ∧
    (∀ V : DerivedCategory A, IsIso (l • 𝟙 V) →
      Subsingleton (V ⟶ ((DerivedCategory.singleFunctor A 0).obj Q)⟦n⟧)) ∧
    (∀ V : DerivedCategory B, IsIso (l • 𝟙 V) →
      Subsingleton (V ⟶ F.mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor A 0).obj P))) ∧
    (∀ V : DerivedCategory B, IsIso (l • 𝟙 V) →
      Subsingleton (V ⟶ F.mapDerivedCategory.obj
        (((DerivedCategory.singleFunctor A 0).obj Q)⟦n⟧))) := by
  have hPdiff : IsIso ((sequenceDifference B l).app (F.obj P)) :=
    sequenceDifference_iso l s (tower_limit_difference l S hS)
  have hQdiff : IsIso ((sequenceDifference B l).app (F.obj Q)) :=
    sequenceDifference_iso l t (tower_limit_difference l H hH)
  have hPnative : IsIso ((sequenceDifference A l).app P) := by
    have : IsIso (F.map ((sequenceDifference A l).app P)) :=
      (sequenceDifference_map_isIso_iff F l P).mpr hPdiff
    exact isIso_of_reflects_iso _ F
  have hQnative : IsIso ((sequenceDifference A l).app Q) := by
    have : IsIso (F.map ((sequenceDifference A l).app Q)) :=
      (sequenceDifference_map_isIso_iff F l Q).mpr hQdiff
    exact isIso_of_reflects_iso _ F
  have hP := complete_of_difference l P hPnative
  have hQ := orthogonal_shift l _ (complete_of_difference l Q hQnative) n
  have hPC := orthogonal_iso l ((F.mapDerivedCategorySingleFunctor 0).app P)
    (complete_of_difference l _ hPdiff)
  have hQC0 := orthogonal_iso l ((F.mapDerivedCategorySingleFunctor 0).app Q)
    (complete_of_difference l _ hQdiff)
  have hQC := orthogonal_iso l ((F.mapDerivedCategory.commShiftIso n).app _)
    (orthogonal_shift l _ hQC0 n)
  exact ⟨hP, hQ, hPC, hQC⟩

end CategoryTheory
