import Langlands.Representation.Aubert.QuasicuspidalJacquetClassStatement
import Langlands.Representation.Aubert.JacquetCompatibilityProof
import Langlands.Representation.Aubert.QuasicuspidalEigenvalue
import Langlands.Representation.Smooth.IrreducibleClassDetection

/-! The sign and actual Jacquet classes of a supplied signed Aubert image. -/

noncomputable section

namespace Langlands.Aubert

open GeneralLinear Parabolic CuspidalSupport SmoothRep
open SmoothRep.IrreducibleGrothendieckProof

universe uF uV

private theorem compositionLength_nonneg {G : Type uF} [Group G] [TopologicalSpace G]
    (A : SmoothRep.{0, uF, uV} ℂ G) (hA : A.HasFiniteLength) :
    0 ≤ FiniteLengthGrothendieckGroup.compositionLength
      (FiniteLengthGrothendieckGroup.ofRepresentation A hA) := by
  obtain ⟨m, s, hs⟩ := chosenSeries ⟨A, hA⟩
  rw [FiniteLengthGrothendieckGroup.compositionLength_of_series A hA s hs]
  exact_mod_cast Nat.zero_le m

private theorem compositionLength_pos {G : Type uF} [Group G] [TopologicalSpace G]
    (A : SmoothRep.{0, uF, uV} ℂ G) (hA : A.HasFiniteLength)
    (hNonzero : Nontrivial A.obj) :
    0 < FiniteLengthGrothendieckGroup.compositionLength
      (FiniteLengthGrothendieckGroup.ofRepresentation A hA) := by
  obtain ⟨m, s, hs⟩ := chosenSeries ⟨A, hA⟩
  rw [FiniteLengthGrothendieckGroup.compositionLength_of_series A hA s hs]
  have hm : m ≠ 0 := by
    intro hm
    have hz : repLength A.representation = 0 := by
      simpa only [hm, Nat.cast_zero] using repLength_eq_of_hasSimpleFactors s hs
    have hzero : Subsingleton A.obj := repLength_eq_zero_iff.mp hz
    obtain ⟨v, w, hvw⟩ := hNonzero.exists_pair_ne
    exact hvw (hzero.elim v w)
  exact_mod_cast Nat.pos_of_ne_zero hm

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Quasicuspidality and positivity determine the sign and the actual
reversed-transport Jacquet class of a supplied signed Aubert image. -/
theorem quasicuspidalJacquetClass :
    QuasicuspidalJacquetClassStatement.{uF, uV} F T := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro n B π τ hπ hτ ε hε hD hqc hNonzero
  let JR := (T.normalizedJacquetFunctor B.reverse).obj π
  let JT := (T.normalizedJacquetFunctor B).obj τ
  let tr := leviTransportK0.{uF, uV} F.Carrier B.reverse B B.reversePermutation
    (conjugatesLevi_reversePermutation F.Carrier B)
  let C := (transportFunctor B.reverse B B.reversePermutation
    (conjugatesLevi_reversePermutation F.Carrier B)).obj JR
  have hJR : JR.HasFiniteLength :=
    normalizedJacquetK0_hasFiniteLength.{uF, uV} F T B.reverse π hπ
  have hJT : JT.HasFiniteLength :=
    normalizedJacquetK0_hasFiniteLength.{uF, uV} F T B τ hτ
  have hC : C.HasFiniteLength :=
    transportFunctor_preservesFiniteLength F.Carrier B.reverse B B.reversePermutation
      (conjugatesLevi_reversePermutation F.Carrier B) JR hJR
  have hCNonzero : Nontrivial C.obj := hNonzero
  have hJRclass :
      normalizedJacquetK0.{uF, uV} F T B.reverse
          (GeneralLinear.finiteLengthClass n F.Carrier π hπ) =
        B.reverse.finiteLengthClass F.Carrier JR hJR :=
    normalizedJacquetK0_finiteLengthClass F T B.reverse π hπ hJR
  have hJTclass :
      normalizedJacquetK0.{uF, uV} F T B
          (GeneralLinear.finiteLengthClass n F.Carrier τ hτ) =
        B.finiteLengthClass F.Carrier JT hJT :=
    normalizedJacquetK0_finiteLengthClass F T B τ hτ hJT
  have hCclass : tr (B.reverse.finiteLengthClass F.Carrier JR hJR) =
      B.finiteLengthClass F.Carrier C hC :=
    leviTransportK0_finiteLengthClass F.Carrier B.reverse B B.reversePermutation
      (conjugatesLevi_reversePermutation F.Carrier B) JR hJR hC
  have hcompat := LinearMap.congr_fun (jacquetCompatibility.{uF, uV} F T n B)
    (GeneralLinear.finiteLengthClass n F.Carrier π hπ)
  change normalizedJacquetK0 F T B
      (alternatingOperator F T n (GeneralLinear.finiteLengthClass n F.Carrier π hπ)) =
    tr (alternatingOperatorOnLevi F T B.reverse
      (normalizedJacquetK0 F T B.reverse
        (GeneralLinear.finiteLengthClass n F.Carrier π hπ))) at hcompat
  rw [hD, map_smul, hJTclass, hJRclass,
    alternatingOperatorOnLevi_quasicuspidal F T B.reverse JR hJR hqc,
    map_smul, hCclass] at hcompat
  have hclasses :
      ε • B.finiteLengthClass F.Carrier JT hJT =
        ((-1 : ℤ) ^ (n - B.length)) • B.finiteLengthClass F.Carrier C hC := hcompat
  have hlength := congrArg
    (FiniteLengthGrothendieckGroup.compositionLength (k := ℂ) (G := B.Levi F.Carrier))
    hclasses
  simp only [map_smul, smul_eq_mul, BlockShape.finiteLengthClass] at hlength
  have hleft := compositionLength_nonneg JT hJT
  have hright := compositionLength_pos C hC hCNonzero
  have hsign : ε = (-1 : ℤ) ^ (n - B.length) := by
    rcases hε with he | he <;>
      rcases neg_one_pow_eq_or ℤ (n - B.length) with hs | hs
    · exact he.trans hs.symm
    · rw [he, hs] at hlength
      simp only [one_mul, neg_one_mul] at hlength
      omega
    · rw [he, hs] at hlength
      simp only [one_mul, neg_one_mul] at hlength
      omega
    · exact he.trans hs.symm
  refine ⟨hsign, ?_⟩
  rw [hJTclass, hJRclass, hCclass]
  rw [← hsign] at hclasses
  rcases hε with he | he <;> simpa only [he, one_smul, neg_one_smul, neg_inj] using hclasses

end Langlands.Aubert
