/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory

import WeilConjectures.AlgebraicGeometry.Pbc.PbcExactCompletionData
import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformReductionCriterion
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleCoefficientHomologyTriangulated
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonFiniteLevel

/-! # Triangulation of the compatible uniform integral category
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

private theorem exactUnitLocus
    {C : Type*} [Category C] [Limits.HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (F : C ⥤ C) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    (η : 𝟭 C ⟶ F) [NatTrans.CommShift η ℤ] :
    ObjectProperty.IsClosedUnderIsomorphisms (fun K ↦ IsIso (η.app K)) ∧
      ObjectProperty.IsTriangulated (fun K ↦ IsIso (η.app K)) := by
  let P : ObjectProperty C := fun K ↦ IsIso (η.app K)
  let : Zero C := Limits.HasZeroObject.zero' C
  have hiso : P.IsClosedUnderIsomorphisms := ⟨by
    intro X Y e hX
    have : IsIso (η.app X) := hX
    have h : η.app Y = e.inv ≫ η.app X ≫ F.map e.hom := by
      simpa using congrArg (fun f ↦ e.inv ≫ f) (η.naturality e.hom)
    change IsIso (η.app Y)
    rw [h]
    infer_instance⟩
  have := hiso
  have hzero : P.ContainsZero := ⟨0, Limits.isZero_zero C,
    (Limits.isZero_zero C).isIso (F.map_isZero (Limits.isZero_zero C)) _⟩
  have hshift : P.IsStableUnderShift ℤ := ⟨fun n ↦ ⟨by
    intro X hX
    have : IsIso (η.app X) := hX
    change IsIso (η.app (X⟦n⟧))
    rw [NatTrans.app_shift η n X]
    infer_instance⟩⟩
  have htri : P.IsTriangulatedClosed₂ := ObjectProperty.IsTriangulatedClosed₂.mk' (by
    intro T hT h₁ h₃
    let φ : T ⟶ F.mapTriangle.obj T :=
      { hom₁ := η.app T.obj₁
        hom₂ := η.app T.obj₂
        hom₃ := η.app T.obj₃
        comm₁ := η.naturality T.mor₁
        comm₂ := η.naturality T.mor₂
        comm₃ := by
          change T.mor₃ ≫ (η.app T.obj₁)⟦(1 : ℤ)⟧' =
            η.app T.obj₃ ≫ F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁
          rw [NatTrans.shift_app]
          simpa using η.naturality_assoc T.mor₃
            ((F.commShiftIso (1 : ℤ)).hom.app T.obj₁) }
    exact Pretriangulated.isIso₂_of_isIso₁₃ φ hT (F.map_distinguished T hT) h₁ h₃)
  refine ⟨hiso, ?_⟩
  exact { toContainsZero := hzero
          toIsStableUnderShift := hshift
          toIsTriangulatedClosed₂ := htri }

private theorem uniformProfileLocus
    {C : Type*} [Category C] [Limits.HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {ι : Type*} (D : ι → Type*) [∀ i, Category (D i)]
    [∀ i, Limits.HasZeroObject (D i)] [∀ i, HasShift (D i) ℤ]
    [∀ i, Preadditive (D i)] [∀ i, ∀ n : ℤ, (shiftFunctor (D i) n).Additive]
    [∀ i, Pretriangulated (D i)]
    (F : ∀ i, C ⥤ D i) [∀ i, (F i).CommShift ℤ] [∀ i, (F i).IsTriangulated]
    (t : ∀ i, Triangulated.TStructure (D i)) (Q : ∀ i, ObjectProperty (D i))
    [∀ i, (Q i).IsClosedUnderIsomorphisms] [∀ i, (Q i).IsTriangulated] :
    let P : ObjectProperty C := fun X ↦ ∃ a b : ℤ, ∀ i,
      (t i).IsGE ((F i).obj X) a ∧ (t i).IsLE ((F i).obj X) b ∧ Q i ((F i).obj X)
    P.IsClosedUnderIsomorphisms ∧ P.IsTriangulated := by
  dsimp only
  let P : ObjectProperty C := fun X ↦ ∃ a b : ℤ, ∀ i,
    (t i).IsGE ((F i).obj X) a ∧ (t i).IsLE ((F i).obj X) b ∧ Q i ((F i).obj X)
  let : Zero C := Limits.HasZeroObject.zero' C
  have hiso : P.IsClosedUnderIsomorphisms := ⟨by
    rintro X Y e ⟨a, b, h⟩
    refine ⟨a, b, fun i ↦ ?_⟩
    have hge := (h i).1
    have hle := (h i).2.1
    exact ⟨(t i).isGE_of_iso ((F i).mapIso e) a,
      (t i).isLE_of_iso ((F i).mapIso e) b, (Q i).prop_of_iso ((F i).mapIso e) (h i).2.2⟩⟩
  have := hiso
  have hzero : P.ContainsZero := ⟨0, Limits.isZero_zero C, 0, 0, fun i ↦
    ⟨(t i).isGE_of_isZero ((F i).map_isZero (Limits.isZero_zero C)) 0,
      (t i).isLE_of_isZero ((F i).map_isZero (Limits.isZero_zero C)) 0,
      (Q i).prop_of_isZero ((F i).map_isZero (Limits.isZero_zero C))⟩⟩
  have hshift : P.IsStableUnderShift ℤ := ⟨fun m ↦ ⟨by
    rintro X ⟨a, b, h⟩
    refine ⟨a - m, b - m, fun i ↦ ?_⟩
    have hge := (h i).1
    have hle := (h i).2.1
    have hgs := (t i).isGE_shift ((F i).obj X) a m (a - m) (by omega)
    have hls := (t i).isLE_shift ((F i).obj X) b m (b - m) (by omega)
    let e : ((F i).obj X)⟦m⟧ ≅ (F i).obj (X⟦m⟧) :=
      ((F i).commShiftIso m |>.app X).symm
    exact ⟨(t i).isGE_of_iso e (a - m),
      (t i).isLE_of_iso e (b - m),
      (Q i).prop_of_iso e
        ((Q i).le_shift m _ (h i).2.2)⟩⟩⟩
  have htri : P.IsTriangulatedClosed₂ := ObjectProperty.IsTriangulatedClosed₂.mk' (by
    rintro T hT ⟨a₁, b₁, h₁⟩ ⟨a₃, b₃, h₃⟩
    refine ⟨min a₁ a₃, max b₁ b₃, fun i ↦ ?_⟩
    have hge₁ := (h₁ i).1
    have hle₁ := (h₁ i).2.1
    have hge₃ := (h₃ i).1
    have hle₃ := (h₃ i).2.1
    have hdist := (F i).map_distinguished T hT
    exact ⟨(t i).isGE₂ _ hdist _
        ((t i).isGE_of_ge ((F i).obj T.obj₁) _ a₁ (min_le_left _ _))
        ((t i).isGE_of_ge ((F i).obj T.obj₃) _ a₃ (min_le_right _ _)),
      (t i).isLE₂ _ hdist _
        ((t i).isLE_of_le ((F i).obj T.obj₁) b₁ _ (le_max_left _ _))
        ((t i).isLE_of_le ((F i).obj T.obj₃) b₃ _ (le_max_right _ _)),
      (Q i).ext_of_isTriangulatedClosed₂ _ hdist (h₁ i).2.2 (h₃ i).2.2⟩)
  refine ⟨hiso, ?_⟩
  exact { toContainsZero := hzero
          toIsStableUnderShift := hshift
          toIsTriangulatedClosed₂ := htri }

/-- The compatible uniform completed integral category is an isomorphism-closed
triangulated full subcategory of its actual ambient derived category. -/
theorem pbcIntegralUniformComplete_isTriangulated (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) [IsNoetherian T]
    (_hDim : ∃ d : ℕ, topologicalKrullDim T ≤ d)
    (_hInv : ∀ t : T, IsUnit (l : T.presheaf.stalk t)) :
    ObjectProperty.IsClosedUnderIsomorphisms.{u + 2, u + 2}
      (C := PbcCompletedDerived T (pbcIntegralDatum l E))
      (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)) ∧
    ObjectProperty.IsTriangulated.{u + 2, u + 2}
      (C := PbcCompletedDerived T (pbcIntegralDatum l E))
      (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)) := by
  let d := pbcIntegralDatum l E
  obtain ⟨F, η, hAdd, hShift, hExact, hUnitShift, hComplete⟩ := pbcExactCompletionData T d
  have := hAdd
  let := hShift
  have := hExact
  have := hUnitShift
  have hCompleteEq : PbcIsIntrinsicallyComplete T d = fun K ↦ IsIso (η.app K) := by
    funext K
    exact propext (hComplete K)
  have hc : ObjectProperty.IsClosedUnderIsomorphisms (PbcIsIntrinsicallyComplete T d) ∧
      ObjectProperty.IsTriangulated (PbcIsIntrinsicallyComplete T d) := by
    rw [hCompleteEq]
    exact exactUnitLocus F η
  have := hc.1
  have := hc.2
  have hred (n : ℕ) : ∃ (_ : (pbcCompletedReduction T d n).CommShift ℤ),
      (pbcCompletedReduction T d n).IsTriangulated :=
    (reductionDerivedExistence T (pbcAdicProjection T d n)).choose_spec.choose_spec.2.1
  let (n : ℕ) : (pbcCompletedReduction T d n).CommShift ℤ := (hred n).choose
  let (n : ℕ) : (pbcCompletedReduction T d n).IsTriangulated := (hred n).choose_spec
  let (n : ℕ) : (pbcDerivedRestrict (pbcLevelConstantComparison T d n).hom).CommShift ℤ := by
    dsimp [pbcDerivedRestrict]
    infer_instance
  let (n : ℕ) : (pbcDerivedRestrict (pbcLevelConstantComparison T d n).hom).IsTriangulated := by
    dsimp [pbcDerivedRestrict]
    infer_instance
  let : ∀ n : ℕ, (pbcConstantReduction T d n).CommShift ℤ := fun n ↦ by
    dsimp [pbcConstantReduction]
    infer_instance
  let : ∀ n : ℕ, (pbcConstantReduction T d n).IsTriangulated := fun n ↦ by
    dsimp [pbcConstantReduction]
    infer_instance
  let Q (n : ℕ) := DerivedCategory.homologyProperty
    (@IsConstructibleProEtaleCoefficientModuleSheaf T (ProEtale.PbcQuotient d n) _
      (d.quotientFinite n))
  let (n : ℕ) : (Q n).IsClosedUnderIsomorphisms :=
    (constructibleCoefficientHomology_isTriangulated T (ProEtale.PbcQuotient d n)).1
  let (n : ℕ) : (Q n).IsTriangulated :=
    (constructibleCoefficientHomology_isTriangulated T (ProEtale.PbcQuotient d n)).2
  have hp := uniformProfileLocus
    (fun n : ℕ ↦ DerivedCategory
      (pbcModules T (adicLisseConstantRing T (ProEtale.PbcQuotient d n))))
    (pbcConstantReduction T d) (fun _ ↦ DerivedCategory.TStructure.t) Q
  change ObjectProperty.IsClosedUnderIsomorphisms (PbcUniformReductionProfile T d) ∧
    ObjectProperty.IsTriangulated (PbcUniformReductionProfile T d) at hp
  have := hp.1
  have := hp.2
  have hPredicate : PbcIsBoundedConstructibleComplete T d =
      (PbcIsIntrinsicallyComplete T d ⊓ PbcUniformReductionProfile T d) := by
    funext K
    exact propext (and_congr_right (fun _ ↦ pbcUniformReductionCriterion l E T K))
  change ObjectProperty.IsClosedUnderIsomorphisms (PbcIsBoundedConstructibleComplete T d) ∧
    ObjectProperty.IsTriangulated (PbcIsBoundedConstructibleComplete T d)
  rw [hPredicate]
  exact ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme
