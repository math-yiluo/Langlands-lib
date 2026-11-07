import Langlands.Global.CurvePlaceCompletionResidue
import Langlands.Global.FunctionFieldPlaceResidueProof
import Langlands.Global.CompletionResidueAdic
import Langlands.Global.AdelicRepresentationHeightPropernessProof
import Mathlib.Data.Nat.Factorial.Basic

/-! # Finite exceptional sets for completed residue cardinalities -/

noncomputable section

universe u

open Polynomial AlgebraicCurve NumberField IsDedekindDomain

namespace Langlands.Global

private theorem finiteField_pow_factorial_succ
    (K : Type u) [Field K] [Finite K] (N : ℕ) (hK : Nat.card K ≤ N) (x : K) :
    x ^ (N.factorial + 1) = x := by
  classical
  let : Fintype K := Fintype.ofFinite K
  by_cases hx : x = 0
  · simp [hx]
  have hcard : 1 < Fintype.card K := Fintype.one_lt_card
  have hdvd : Fintype.card K - 1 ∣ N.factorial :=
    Nat.dvd_factorial (by omega)
      (by rw [Nat.card_eq_fintype_card] at hK; omega)
  obtain ⟨m, hm⟩ := hdvd
  rw [hm, pow_succ, pow_mul, FiniteField.pow_card_sub_one_eq_one x hx, one_pow, one_mul]

section FunctionField

variable (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]

/-- Only finitely many actual curve places have residue cardinality bounded
by a given natural number. -/
theorem curvePlace_finite_small_residue (N : ℕ) :
    {v : Place k F | Nat.card v.ResidueField ≤ N}.Finite := by
  let s : F := algebraMap (RatFunc k) F (RatFunc.X : RatFunc k)
  have hs : Transcendental k s :=
    (transcendental_algebraMap_iff (algebraMap (RatFunc k) F).injective).mpr
      RatFunc.transcendental_X
  have ha : s ^ (N.factorial + 1) - s ≠ 0 := by
    intro h
    have hz : aeval s (X ^ (N.factorial + 1) - X : k[X]) = 0 := by
      simpa only [map_sub, map_pow, aeval_X] using h
    exact FiniteField.X_pow_card_sub_X_ne_zero k
      (by have := Nat.factorial_pos N; omega) ((transcendental_iff.mp hs) _ hz)
  apply ((curvePlaceFinitePoles k F s).union
    (curvePlaceFinitePoles k F (s ^ (N.factorial + 1) - s)⁻¹)).subset
  intro v hv
  by_cases hvs : s ∈ v.toValuationSubring
  · apply Or.inr
    let : Module.Finite k v.ResidueField := functionFieldPlaceResidue k F v
    let : Finite v.ResidueField := Module.finite_of_finite k
    let x : v.toValuationSubring := ⟨s, hvs⟩
    have hroot : IsLocalRing.residue v.toValuationSubring
        (x ^ (N.factorial + 1) - x) = 0 := by
      rw [map_sub, map_pow, sub_eq_zero]
      exact finiteField_pow_factorial_succ v.ResidueField N hv _
    have hnonunit : s ^ (N.factorial + 1) - s ∈ v.toValuationSubring.nonunits :=
      ValuationSubring.coe_mem_nonunits_iff.mpr
        ((IsLocalRing.residue_eq_zero_iff _).mp hroot)
    exact ((ValuationSubring.mem_nonunits_iff_or v.toValuationSubring).mp hnonunit).resolve_left ha
  · exact Or.inl hvs

/-- Bounded completed residue cardinality occurs at only finitely many
actual curve places. -/
theorem curvePlaceCompletion_finite_small_residue (B : ℝ) :
    {v : Place k F |
      (Nat.card (IsLocalRing.ResidueField (curvePlaceCompletionIntegers v)) : ℝ) ≤ B}.Finite := by
  apply (curvePlace_finite_small_residue k F ⌊B⌋₊).subset
  intro v hv
  have he := Nat.card_congr (curvePlaceCompletionResidueEquiv v).toEquiv
  exact Nat.le_floor (by rwa [he])

/-- The exact finite exceptional set for a real completed residue-cardinality
bound in a global function field. -/
def curvePlaceSmallCompletionResiduePlaces (B : ℝ) : Finset (Place k F) :=
  (curvePlaceCompletion_finite_small_residue k F B).toFinset

@[simp]
theorem mem_curvePlaceSmallCompletionResiduePlaces (B : ℝ) (v : Place k F) :
    v ∈ curvePlaceSmallCompletionResiduePlaces k F B ↔
      (Nat.card (IsLocalRing.ResidueField (curvePlaceCompletionIntegers v)) : ℝ) ≤ B :=
  Set.Finite.mem_toFinset _

theorem curvePlaceSmallCompletionResiduePlaces_lt (B : ℝ) (v : Place k F)
    (hv : v ∉ curvePlaceSmallCompletionResiduePlaces k F B) :
    B < (Nat.card (IsLocalRing.ResidueField (curvePlaceCompletionIntegers v)) : ℝ) :=
  lt_of_not_ge (fun h => hv ((mem_curvePlaceSmallCompletionResiduePlaces k F B v).mpr h))

end FunctionField

section NumberField

variable (K : Type u) [Field K] [NumberField K]

/-- Bounded completed residue cardinality occurs at only finitely many
finite places of a number field. -/
theorem finitePlaceCompletion_finite_small_residue (B : ℝ) :
    {v : FinitePlace K |
      (Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) : ℝ) ≤ B}.Finite := by
  simpa only [CompletionResidue.card_adicResidueField] using
    AdelicMatrixHeight.finite_absNorm_le K B

/-- The exact finite exceptional set for a real completed residue-cardinality
bound in a number field. -/
def finitePlaceSmallCompletionResiduePlaces (B : ℝ) : Finset (FinitePlace K) :=
  (finitePlaceCompletion_finite_small_residue K B).toFinset

@[simp]
theorem mem_finitePlaceSmallCompletionResiduePlaces (B : ℝ) (v : FinitePlace K) :
    v ∈ finitePlaceSmallCompletionResiduePlaces K B ↔
      (Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) : ℝ) ≤ B :=
  Set.Finite.mem_toFinset _

theorem finitePlaceSmallCompletionResiduePlaces_lt (B : ℝ) (v : FinitePlace K)
    (hv : v ∉ finitePlaceSmallCompletionResiduePlaces K B) :
    B < (Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) : ℝ) :=
  lt_of_not_ge (fun h => hv ((mem_finitePlaceSmallCompletionResiduePlaces K B v).mpr h))

end NumberField

end Langlands.Global
