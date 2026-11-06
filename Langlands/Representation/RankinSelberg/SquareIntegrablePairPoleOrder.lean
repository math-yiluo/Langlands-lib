import Langlands.Representation.RankinSelberg.SupercuspidalPairPoleOrder
import Langlands.Representation.RankinSelberg.PadicPairLPolynomialNormalization
import Langlands.Representation.Classification.SupercuspidalTwist
import Langlands.Representation.Twist.SubquotientProof

/-!
# Pole orders at `s = 0` from JPSS 1983, Theorem (8.2)

Let `π` and `σ` be essentially square-integrable components of the inductions
of the centered segments `π₀ ⊗ α^(m/2), …, π₀ ⊗ α^(-m/2)` and
`σ₀ ⊗ α^(n/2), …, σ₀ ⊗ α^(-n/2)` of irreducible supercuspidal representations.
Assuming the statements of JPSS 1983, Proposition (8.1) and Theorem (8.2), the
order of the pole of `L(s, π × σ)` at `s = 0` is the number of `j` with
`π₀ ⊗ α^(m/2) ≅ (σ₀ ⊗ α^(n/2 - j))^∨` when `π₀` and `σ₀` have the same rank, and
`0` otherwise.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial

universe uF uV uW uV₂ uW₂

variable {p : ℕ} [Fact p.Prime]

/-- Twisting by a real power `|det|^s` preserves and reflects supercuspidality. -/
theorem isSupercuspidal_realPowerTwist_iff {F : PadicField.{uF} p} (n : ℕ) (s : ℝ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Langlands.GeneralLinear n F.Carrier) V) :
    letI := F.canonicalTopologicalData.topology
    GeneralLinear.IsSupercuspidal
        (realPowerTwist (F.canonicalTopologicalData.determinantNorm n) s ρ) ↔
      GeneralLinear.IsSupercuspidal ρ :=
  letI := F.canonicalTopologicalData.topology
  isSupercuspidal_twist_iff (F.canonicalTopologicalData.determinantPowerCharacter n s)
    (F.canonicalTopologicalData.isOpen_ker_determinantPowerCharacter n s)
    (F.canonicalTopologicalData.ker_determinant_le_ker_determinantPowerCharacter n s) ρ

/-- The blocks of a centered segment of an irreducible representation are irreducible. -/
theorem isIrreducible_centeredSegmentBlocks {F : PadicField.{uF} p} {a : ℕ} (m : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {π₀ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V}
    (hπ₀ : Representation.IsIrreducible π₀) (i : Fin (m + 1)) :
    Representation.IsIrreducible (centeredSegmentBlocks F m π₀ i) :=
  (isIrreducible_twist_iff _ π₀).mpr hπ₀

/-- The blocks of a centered segment of a supercuspidal representation are
supercuspidal. -/
theorem isSupercuspidal_centeredSegmentBlocks {F : PadicField.{uF} p} {a : ℕ} (m : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {π₀ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V}
    (hπ₀ : letI := F.canonicalTopologicalData.topology; GeneralLinear.IsSupercuspidal π₀)
    (i : Fin (m + 1)) :
    letI := F.canonicalTopologicalData.topology
    GeneralLinear.IsSupercuspidal (centeredSegmentBlocks F m π₀ i) :=
  (isSupercuspidal_realPowerTwist_iff (a + 1) _ π₀).mpr hπ₀

/-- The count `∑_(j = 0)^n [π₀ ⊗ α^(m/2) ≅ (σ₀ ⊗ α^(n/2 - j))^∨]` for two
representations `π₀` and `σ₀` of the same group `GL_(a+1)(F)`, where `α = |det|`
and `^∨` is the smooth contragredient. The term `j` compares the first block of
the centered segment of `π₀` of length `m + 1` with the contragredient of the
block `j` of the centered segment of `σ₀` of length `n + 1`. -/
def centeredSegmentPoleCount (F : PadicField.{uF} p) {a : ℕ} (m n : ℕ)
    {V₀ : Type uV} [AddCommGroup V₀] [Module ℂ V₀]
    {W₀ : Type uW} [AddCommGroup W₀] [Module ℂ W₀]
    (π₀ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V₀)
    (σ₀ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) W₀) : ℕ :=
  ∑ j : Fin (n + 1),
    contragredientIndicator F (centeredSegmentBlocks F m π₀ 0) (centeredSegmentBlocks F n σ₀ j)

/-- The polynomial `1` has pole order `0` at `s = 0`. -/
theorem lPolynomialPoleOrderAtZero_one : lPolynomialPoleOrderAtZero (1 : ℂ[X]) = 0 :=
  rootMultiplicity_eq_zero (by simp)

section EightTwo

variable {F : PadicField.{uF} p}
  {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
  {V₀ : Type uV} [AddCommGroup V₀] [Module ℂ V₀]
  {W₀ : Type uW} [AddCommGroup W₀] [Module ℂ W₀]
  {V : Type uV₂} [AddCommGroup V] [Module ℂ V]
  {W : Type uW₂} [AddCommGroup W] [Module ℂ W]

/-- JPSS 1983, Theorem (8.2) with Proposition (8.1)(ii), at `s = 0`, for
supercuspidal supports of equal rank and `t ≤ r`: the pole order of
`L(s, π × σ)` at `s = 0` is `centeredSegmentPoleCount F m n π₀ σ₀`. -/
theorem lPolynomialPoleOrderAtZero_of_squareIntegrable_equalRank
    (h82 : SquareIntegrableLFactorStatement.{uF, uV, uW, uV₂, uW₂})
    (h81 : SupercuspidalEqualRankLFactorStatement.{uF, uV, uW})
    {a m r n t : ℕ} (hr : ∑ _i : Fin (m + 1), (a + 1) = r + 1)
    (ht : ∑ _j : Fin (n + 1), (a + 1) = t + 1)
    {π₀ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V₀}
    {σ₀ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) W₀}
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W}
    (hπ₀ : Representation.IsIrreducible π₀)
    (hπ₀s : letI := F.canonicalTopologicalData.topology; GeneralLinear.IsSupercuspidal π₀)
    (hσ₀ : Representation.IsIrreducible σ₀)
    (hσ₀s : letI := F.canonicalTopologicalData.topology; GeneralLinear.IsSupercuspidal σ₀)
    (hπ : F.canonicalTopologicalData.IsEssentiallySquareIntegrable π)
    (hπc : IsIrreducibleComponent
      (F.canonicalNormalizedProductInduced (succBlockShape (fun _ => a) hr)
        (centeredSegmentBlocks F m π₀)) π)
    (hσ : F.canonicalTopologicalData.IsEssentiallySquareIntegrable σ)
    (hσc : IsIrreducibleComponent
      (F.canonicalNormalizedProductInduced (succBlockShape (fun _ => a) ht)
        (centeredSegmentBlocks F n σ₀)) σ)
    (htr : t ≤ r)
    (hσw : ∀ j, letI := F.canonicalTopologicalData.topology
      IsOfWhittakerType a (standardCharacter ψ a) (centeredSegmentBlocks F n σ₀ j))
    {P : ℂ[X]} (hP : IsPadicPairLPolynomial F ψ ν.val π σ P) :
    lPolynomialPoleOrderAtZero P = centeredSegmentPoleCount F m n π₀ σ₀ := by
  obtain ⟨P', Q, hP', hQ, hPQ⟩ :=
    h82 p F ψ ν a m r a n t hr ht π₀ σ₀ π σ hπ₀ hπ₀s hσ₀ hσ₀s hπ hπc hσ hσc htr
  rw [hP.unique hP', hPQ, lPolynomialPoleOrderAtZero_prod _ _ fun j _ =>
    ne_zero_of_coeff_zero_eq_one (hQ j).coeff_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact lPolynomialPoleOrderAtZero_of_supercuspidalEqualRank h81 ν
    (isIrreducible_centeredSegmentBlocks m hπ₀ 0)
    (isSupercuspidal_centeredSegmentBlocks m hπ₀s 0)
    (isIrreducible_centeredSegmentBlocks n hσ₀ j) (hσw j)
    ((isPadicSymmetricLPolynomial_of_le le_rfl).mp (hQ j))

/-- JPSS 1983, Theorem (8.2) with Proposition (8.1)(i), at `s = 0`, for
supercuspidal supports of different ranks and `t ≤ r`: `L(s, π × σ)` has no
pole at `s = 0`. -/
theorem lPolynomialPoleOrderAtZero_of_squareIntegrable_ne_rank
    (h82 : SquareIntegrableLFactorStatement.{uF, uV, uW, uV₂, uW₂})
    (h81 : SupercuspidalUnequalRankLFactorStatement.{uF, uV, uW})
    (h81' : SupercuspidalUnequalRankLFactorStatement.{uF, uW, uV})
    {a m r b n t : ℕ} (hr : ∑ _i : Fin (m + 1), (a + 1) = r + 1)
    (ht : ∑ _j : Fin (n + 1), (b + 1) = t + 1) (hab : a ≠ b)
    {π₀ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V₀}
    {σ₀ : Representation ℂ (Langlands.GeneralLinear (b + 1) F.Carrier) W₀}
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W}
    (hπ₀ : Representation.IsIrreducible π₀)
    (hπ₀s : letI := F.canonicalTopologicalData.topology; GeneralLinear.IsSupercuspidal π₀)
    (hσ₀ : Representation.IsIrreducible σ₀)
    (hσ₀s : letI := F.canonicalTopologicalData.topology; GeneralLinear.IsSupercuspidal σ₀)
    (hπ : F.canonicalTopologicalData.IsEssentiallySquareIntegrable π)
    (hπc : IsIrreducibleComponent
      (F.canonicalNormalizedProductInduced (succBlockShape (fun _ => a) hr)
        (centeredSegmentBlocks F m π₀)) π)
    (hσ : F.canonicalTopologicalData.IsEssentiallySquareIntegrable σ)
    (hσc : IsIrreducibleComponent
      (F.canonicalNormalizedProductInduced (succBlockShape (fun _ => b) ht)
        (centeredSegmentBlocks F n σ₀)) σ)
    (htr : t ≤ r)
    (hπw : letI := F.canonicalTopologicalData.topology
      IsOfWhittakerType a (standardCharacter ψ a) (centeredSegmentBlocks F m π₀ 0))
    (hσw : ∀ j, letI := F.canonicalTopologicalData.topology
      IsOfWhittakerType b (standardCharacter ψ b) (centeredSegmentBlocks F n σ₀ j))
    {P : ℂ[X]} (hP : IsPadicPairLPolynomial F ψ ν.val π σ P) :
    lPolynomialPoleOrderAtZero P = 0 := by
  obtain ⟨P', Q, hP', hQ, hPQ⟩ :=
    h82 p F ψ ν a m r b n t hr ht π₀ σ₀ π σ hπ₀ hπ₀s hσ₀ hσ₀s hπ hπc hσ hσc htr
  have hQ1 : ∀ j, Q j = 1 := by
    intro j
    rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
    · have h1 := h81' p F ψ ν b a (centeredSegmentBlocks F n σ₀ j)
        (centeredSegmentBlocks F m π₀ 0) (isIrreducible_centeredSegmentBlocks n hσ₀ j)
        (isSupercuspidal_centeredSegmentBlocks n hσ₀s j) hπw hlt
      exact ((isPadicSymmetricLPolynomial_of_lt hlt).mp (hQ j)).unique h1
    · have h1 := h81 p F ψ ν a b (centeredSegmentBlocks F m π₀ 0)
        (centeredSegmentBlocks F n σ₀ j) (isIrreducible_centeredSegmentBlocks m hπ₀ 0)
        (isSupercuspidal_centeredSegmentBlocks m hπ₀s 0) (hσw j) hlt
      exact ((isPadicSymmetricLPolynomial_of_le hlt.le).mp (hQ j)).unique h1
  rw [hP.unique hP', hPQ, Finset.prod_congr rfl fun j _ => hQ1 j, Finset.prod_const_one,
    lPolynomialPoleOrderAtZero_one]

/-- With `(m + 1)(a + 1) = r + 1` and `(n + 1)(a + 1) = t + 1`, `t ≤ r` exactly when
`n ≤ m`. -/
theorem le_iff_of_centeredSegment_rank {a m r n t : ℕ}
    (hr : ∑ _i : Fin (m + 1), (a + 1) = r + 1) (ht : ∑ _j : Fin (n + 1), (a + 1) = t + 1) :
    t ≤ r ↔ n ≤ m := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hr ht
  rw [← Nat.add_le_add_iff_right (n := 1), ← hr, ← ht, Nat.mul_le_mul_right_iff (Nat.succ_pos a),
    Nat.add_le_add_iff_right]

/-- JPSS 1983, Theorem (8.2) with Proposition (8.1)(ii), at `s = 0`, for
supercuspidal supports of equal rank, in either rank order: the pole order of
`L(s, π × σ)` at `s = 0` is `centeredSegmentPoleCount F m n π₀ σ₀` when `n ≤ m`,
and `centeredSegmentPoleCount F n m σ₀ π₀` otherwise. -/
theorem lPolynomialPoleOrderAtZero_of_squareIntegrable_symmetric_equalRank
    (h82 : SquareIntegrableLFactorStatement.{uF, uV, uW, uV₂, uW₂})
    (h82' : SquareIntegrableLFactorStatement.{uF, uW, uV, uW₂, uV₂})
    (h81 : SupercuspidalEqualRankLFactorStatement.{uF, uV, uW})
    (h81' : SupercuspidalEqualRankLFactorStatement.{uF, uW, uV})
    {a m r n t : ℕ} (hr : ∑ _i : Fin (m + 1), (a + 1) = r + 1)
    (ht : ∑ _j : Fin (n + 1), (a + 1) = t + 1)
    {π₀ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V₀}
    {σ₀ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) W₀}
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W}
    (hπ₀ : Representation.IsIrreducible π₀)
    (hπ₀s : letI := F.canonicalTopologicalData.topology; GeneralLinear.IsSupercuspidal π₀)
    (hσ₀ : Representation.IsIrreducible σ₀)
    (hσ₀s : letI := F.canonicalTopologicalData.topology; GeneralLinear.IsSupercuspidal σ₀)
    (hπ : F.canonicalTopologicalData.IsEssentiallySquareIntegrable π)
    (hπc : IsIrreducibleComponent
      (F.canonicalNormalizedProductInduced (succBlockShape (fun _ => a) hr)
        (centeredSegmentBlocks F m π₀)) π)
    (hσ : F.canonicalTopologicalData.IsEssentiallySquareIntegrable σ)
    (hσc : IsIrreducibleComponent
      (F.canonicalNormalizedProductInduced (succBlockShape (fun _ => a) ht)
        (centeredSegmentBlocks F n σ₀)) σ)
    (hπw : ∀ i, letI := F.canonicalTopologicalData.topology
      IsOfWhittakerType a (standardCharacter ψ a) (centeredSegmentBlocks F m π₀ i))
    (hσw : ∀ j, letI := F.canonicalTopologicalData.topology
      IsOfWhittakerType a (standardCharacter ψ a) (centeredSegmentBlocks F n σ₀ j))
    {P : ℂ[X]} (hP : IsPadicSymmetricLPolynomial F ψ ν.val π σ P) :
    lPolynomialPoleOrderAtZero P =
      if n ≤ m then centeredSegmentPoleCount F m n π₀ σ₀
      else centeredSegmentPoleCount F n m σ₀ π₀ := by
  by_cases htr : t ≤ r
  · rw [ite_eq_left ((le_iff_of_centeredSegment_rank hr ht).mp htr)]
    exact lPolynomialPoleOrderAtZero_of_squareIntegrable_equalRank ν h82 h81 hr ht hπ₀ hπ₀s
      hσ₀ hσ₀s hπ hπc hσ hσc htr hσw ((isPadicSymmetricLPolynomial_of_le htr).mp hP)
  · rw [ite_eq_right (mt (le_iff_of_centeredSegment_rank hr ht).mpr htr)]
    have hrt : r < t := Nat.lt_of_not_le htr
    exact lPolynomialPoleOrderAtZero_of_squareIntegrable_equalRank ν h82' h81' ht hr hσ₀ hσ₀s
      hπ₀ hπ₀s hσ hσc hπ hπc hrt.le hπw ((isPadicSymmetricLPolynomial_of_lt hrt).mp hP)

/-- JPSS 1983, Theorem (8.2) with Proposition (8.1)(i), at `s = 0`, for
supercuspidal supports of different ranks, in either rank order: `L(s, π × σ)`
has no pole at `s = 0`. -/
theorem lPolynomialPoleOrderAtZero_of_squareIntegrable_symmetric_ne_rank
    (h82 : SquareIntegrableLFactorStatement.{uF, uV, uW, uV₂, uW₂})
    (h82' : SquareIntegrableLFactorStatement.{uF, uW, uV, uW₂, uV₂})
    (h81 : SupercuspidalUnequalRankLFactorStatement.{uF, uV, uW})
    (h81' : SupercuspidalUnequalRankLFactorStatement.{uF, uW, uV})
    {a m r b n t : ℕ} (hr : ∑ _i : Fin (m + 1), (a + 1) = r + 1)
    (ht : ∑ _j : Fin (n + 1), (b + 1) = t + 1) (hab : a ≠ b)
    {π₀ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V₀}
    {σ₀ : Representation ℂ (Langlands.GeneralLinear (b + 1) F.Carrier) W₀}
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W}
    (hπ₀ : Representation.IsIrreducible π₀)
    (hπ₀s : letI := F.canonicalTopologicalData.topology; GeneralLinear.IsSupercuspidal π₀)
    (hσ₀ : Representation.IsIrreducible σ₀)
    (hσ₀s : letI := F.canonicalTopologicalData.topology; GeneralLinear.IsSupercuspidal σ₀)
    (hπ : F.canonicalTopologicalData.IsEssentiallySquareIntegrable π)
    (hπc : IsIrreducibleComponent
      (F.canonicalNormalizedProductInduced (succBlockShape (fun _ => a) hr)
        (centeredSegmentBlocks F m π₀)) π)
    (hσ : F.canonicalTopologicalData.IsEssentiallySquareIntegrable σ)
    (hσc : IsIrreducibleComponent
      (F.canonicalNormalizedProductInduced (succBlockShape (fun _ => b) ht)
        (centeredSegmentBlocks F n σ₀)) σ)
    (hπw : ∀ i, letI := F.canonicalTopologicalData.topology
      IsOfWhittakerType a (standardCharacter ψ a) (centeredSegmentBlocks F m π₀ i))
    (hσw : ∀ j, letI := F.canonicalTopologicalData.topology
      IsOfWhittakerType b (standardCharacter ψ b) (centeredSegmentBlocks F n σ₀ j))
    {P : ℂ[X]} (hP : IsPadicSymmetricLPolynomial F ψ ν.val π σ P) :
    lPolynomialPoleOrderAtZero P = 0 := by
  by_cases htr : t ≤ r
  · exact lPolynomialPoleOrderAtZero_of_squareIntegrable_ne_rank ν h82 h81 h81' hr ht hab
      hπ₀ hπ₀s hσ₀ hσ₀s hπ hπc hσ hσc htr (hπw 0) hσw
      ((isPadicSymmetricLPolynomial_of_le htr).mp hP)
  · have hrt : r < t := Nat.lt_of_not_le htr
    exact lPolynomialPoleOrderAtZero_of_squareIntegrable_ne_rank ν h82' h81' h81 ht hr
      hab.symm hσ₀ hσ₀s hπ₀ hπ₀s hσ hσc hπ hπc hrt.le (hσw 0) hπw
      ((isPadicSymmetricLPolynomial_of_lt hrt).mp hP)

end EightTwo

end Langlands.RankinSelberg
