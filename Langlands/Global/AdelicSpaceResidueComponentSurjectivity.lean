import Langlands.AlgebraicGeometry.AlgebraicSpace.UniformLangWeilFiniteFieldLifts
import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianSmoothPointLifting
import Langlands.Global.AdelicLevelModelPoints
import Langlands.Global.CompletionIntegersSmoothPointLifting
import Langlands.Global.CompletionResidueBounds

/-! # Almost-all algebraic-space level surjectivity from residue estimates -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace
open NumberField

namespace Langlands.Global

/-- Choose actual point lifts outside a finite exceptional index set from
cofinite surjectivity of the actual coefficient-ring point maps. -/
def cofiniteSpacePointLifts
    {I C : Type u} [CommRing C]
    (R : I → Type u) [∀ i, CommRing (R i)] [∀ i, Algebra C (R i)]
    {X Y : AlgebraicSpace (Spec (CommRingCat.of C))} (f : X ⟶ Y)
    (hs : ∀ᶠ i in Filter.cofinite,
      Function.Surjective (RingPoints.map (A := R i) f)) :
    Σ E : Finset I, (i : I) → i ∉ E →
      (p : RingPoints C Y (R i)) → {q : RingPoints C X (R i) // RingPoints.map f q = p} := by
  classical
  let bad := Filter.eventually_cofinite.mp hs
  refine ⟨bad.toFinset, fun i hi p => ?_⟩
  have hsurj : Function.Surjective (RingPoints.map (A := R i) f) := by
    by_contra h
    exact hi (bad.mem_toFinset.mpr h)
  exact ⟨(hsurj p).choose, (hsurj p).choose_spec⟩

section Curve

variable (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
  (S : Finset (AlgebraicCurve.Place k F))
  {X Y : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))}

/-- A common numerical estimate on actual residue-point fibres implies
surjectivity on cofinitely many actual curve-place level factors. -/
theorem curvePlaceSpaceFactor_eventually_surjective_of_residue_bound
    (f : X ⟶ Y) (hf : IsSmoothMorphism f)
    (d : ℕ) {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ (v : {v : AlgebraicCurve.Place k F // v ∉ S})
      (x : RingPoints (curvePlaceSIntegers k F S) Y
        (IsLocalRing.ResidueField (CurvePlaceLevelFactor k F S (.inr v)))),
      |(Nat.card {y : RingPoints (curvePlaceSIntegers k F S) X
          (IsLocalRing.ResidueField (CurvePlaceLevelFactor k F S (.inr v))) //
          RingPoints.map f y = x} : ℝ) -
          (Nat.card (IsLocalRing.ResidueField
            (CurvePlaceLevelFactor k F S (.inr v))) : ℝ) ^ d| ≤
        c * (Nat.card (IsLocalRing.ResidueField
          (CurvePlaceLevelFactor k F S (.inr v))) : ℝ) ^ ((d : ℝ) - 1 / 2)) :
    ∀ᶠ i in Filter.cofinite,
      Function.Surjective (RingPoints.map (A := CurvePlaceLevelFactor k F S i) f) := by
  classical
  let small : Set {v : AlgebraicCurve.Place k F // v ∉ S} :=
    {v | (Nat.card (IsLocalRing.ResidueField (curvePlaceCompletionIntegers v.1)) : ℝ) ≤ c ^ 2}
  have hsmall : small.Finite :=
    (curvePlaceCompletion_finite_small_residue k F (c ^ 2)).preimage
      Subtype.val_injective.injOn
  apply Filter.eventually_cofinite.mpr
  apply ((Set.finite_range
    (Sum.inl : {v : AlgebraicCurve.Place k F // v ∈ S} → CurvePlaceLevelFactorIndex k F S)).union
    (hsmall.image Sum.inr)).subset
  intro i hi
  rcases i with v | v
  · exact Or.inl ⟨v, rfl⟩
  · apply Or.inr
    refine ⟨v, ?_, rfl⟩
    by_contra hv
    have hlarge : c ^ 2 < (Nat.card (IsLocalRing.ResidueField
        (CurvePlaceLevelFactor k F S (.inr v))) : ℝ) := lt_of_not_ge hv
    let O := CurvePlaceLevelFactor k F S (.inr v)
    let : HenselianLocalRing O := curvePlaceCompletionIntegers_henselian v.1
    exact hi (HenselianSmoothPointLifting.surjective_of_residue f hf
      (IsScalarTower.toAlgHom (curvePlaceSIntegers k F S) O (IsLocalRing.ResidueField O))
      IsLocalRing.residue_surjective
      (UniformLangWeilFiniteFieldLifts.surjective_of_bound f d hc hlarge (hbound v)))

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
  {X Y : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))}

/-- The same residue estimate gives cofinite surjectivity on the full
number-field level index, which includes every infinite place. -/
theorem numberFieldSpaceFactor_eventually_surjective_of_residue_bound
    (f : X ⟶ Y) (hf : IsSmoothMorphism f)
    (d : ℕ) {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ (v : {v : FinitePlace K // v ∉ S})
      (x : RingPoints ((S : Set (FinitePlace K)).integer K) Y
        (IsLocalRing.ResidueField (NumberFieldLevelFactor K S (.inr (.inr v))))),
      |(Nat.card {y : RingPoints ((S : Set (FinitePlace K)).integer K) X
          (IsLocalRing.ResidueField (NumberFieldLevelFactor K S (.inr (.inr v)))) //
          RingPoints.map f y = x} : ℝ) -
          (Nat.card (IsLocalRing.ResidueField
            (NumberFieldLevelFactor K S (.inr (.inr v)))) : ℝ) ^ d| ≤
        c * (Nat.card (IsLocalRing.ResidueField
          (NumberFieldLevelFactor K S (.inr (.inr v)))) : ℝ) ^ ((d : ℝ) - 1 / 2)) :
    ∀ᶠ i in Filter.cofinite,
      Function.Surjective (RingPoints.map (A := NumberFieldLevelFactor K S i) f) := by
  classical
  let small : Set {v : FinitePlace K // v ∉ S} :=
    {v | (Nat.card (IsLocalRing.ResidueField (v.1.adicCompletionIntegers K)) : ℝ) ≤ c ^ 2}
  have hsmall : small.Finite :=
    (finitePlaceCompletion_finite_small_residue K (c ^ 2)).preimage
      Subtype.val_injective.injOn
  apply Filter.eventually_cofinite.mpr
  apply (((Set.finite_range
    (Sum.inl : InfinitePlace K → NumberFieldLevelFactorIndex K S)).union
    (Set.finite_range
      (fun v : {v : FinitePlace K // v ∈ S} =>
        (Sum.inr (Sum.inl v) : NumberFieldLevelFactorIndex K S)))).union
    (hsmall.image (fun v => Sum.inr (Sum.inr v)))).subset
  intro i hi
  rcases i with v | v | v
  · exact Or.inl (Or.inl ⟨v, rfl⟩)
  · exact Or.inl (Or.inr ⟨v, rfl⟩)
  · apply Or.inr
    refine ⟨v, ?_, rfl⟩
    by_contra hv
    have hlarge : c ^ 2 < (Nat.card (IsLocalRing.ResidueField
        (NumberFieldLevelFactor K S (.inr (.inr v)))) : ℝ) := lt_of_not_ge hv
    let O := NumberFieldLevelFactor K S (.inr (.inr v))
    let : HenselianLocalRing O := adicCompletionIntegers_henselian (RingOfIntegers K) K v.1
    exact hi (HenselianSmoothPointLifting.surjective_of_residue f hf
      (IsScalarTower.toAlgHom ((S : Set (FinitePlace K)).integer K)
        O (IsLocalRing.ResidueField O))
      IsLocalRing.residue_surjective
      (UniformLangWeilFiniteFieldLifts.surjective_of_bound f d hc hlarge (hbound v)))

end NumberField

end Langlands.Global
