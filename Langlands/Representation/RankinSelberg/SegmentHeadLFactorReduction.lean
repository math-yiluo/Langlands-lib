import Langlands.Representation.RankinSelberg.IrreducibleComponentEmbedding
import Langlands.Representation.RankinSelberg.SegmentFactorStatement
import Langlands.Representation.RankinSelberg.SquareIntegrablePairPoleOrder
import Langlands.Representation.RankinSelberg.SupercuspidalUnequalRankLFactorReduction
import Langlands.Representation.RankinSelberg.SupercuspidalProductGamma
import Langlands.Representation.RankinSelberg.TemperedTwistSupercuspidalPoleTransport
import Langlands.Representation.RankinSelberg.TemperedLFactorDivisibility
import Langlands.Representation.Classification.SegmentHeadDecreasingSocle
import Langlands.Representation.Classification.SegmentUniverseLift
import Langlands.Representation.Classification.SegmentSpecialEssentialSquareIntegrabilityProof

/-!
# The segment-head L-factor formula from JPSS 1983, Theorem (8.2)

Henniart 2002, §2.6 (`SegmentHeadLFactorStatement`) follows from JPSS 1983,
Theorem (8.2) (`SquareIntegrableLFactorStatement`), which is the only premise.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial
open PadicField.TopologicalData

universe uF uV uW

variable {p : ℕ} [Fact p.Prime]


section Rank

variable {F : PadicField.{uF} p}
  {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
  {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier}
  {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The arbitrary-rank L-polynomial relation is symmetric in the pair. -/
theorem isPadicRankLPolynomial_comm {n t : ℕ}
    (π : Representation ℂ (Langlands.GeneralLinear n F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear t F.Carrier) W) (P : ℂ[X]) :
    IsPadicRankLPolynomial F ψ ν π σ P ↔ IsPadicRankLPolynomial F ψ ν σ π P := by
  cases n with
  | zero => cases t <;> exact Iff.rfl
  | succ n =>
    cases t with
    | zero => exact Iff.rfl
    | succ t => exact TemperedLFactorDivisibility.symmetricLPolynomial_swap F ψ ν π σ P

/-- A real determinant twist of the second member moves to the first:
`L(s, ν^x π × ν^y σ) = L(s, ν^(x+y) π × σ)`. -/
theorem isPadicRankLPolynomial_realPowerTwist_move {n t : ℕ}
    (π : Representation ℂ (Langlands.GeneralLinear n F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear t F.Carrier) W) (x y : ℝ) (P : ℂ[X]) :
    IsPadicRankLPolynomial F ψ ν
        (realPowerTwist (F.canonicalTopologicalData.determinantNorm n) x π)
        (realPowerTwist (F.canonicalTopologicalData.determinantNorm t) y σ) P ↔
      IsPadicRankLPolynomial F ψ ν
        (realPowerTwist (F.canonicalTopologicalData.determinantNorm n) (x + y) π) σ P := by
  rw [← isPadicRankLPolynomial_realPowerTwist ψ ν
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm n) (x + y) π) σ (-y) P,
    ← realPowerTwist_add, neg_neg, show -y + (x + y) = x by ring]

/-- `L(s, ν^x π × σ) = L(s, ν^x σ × π)`. -/
theorem isPadicRankLPolynomial_realPowerTwist_comm {n t : ℕ}
    (π : Representation ℂ (Langlands.GeneralLinear n F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear t F.Carrier) W) (x : ℝ) (P : ℂ[X]) :
    IsPadicRankLPolynomial F ψ ν
        (realPowerTwist (F.canonicalTopologicalData.determinantNorm n) x π) σ P ↔
      IsPadicRankLPolynomial F ψ ν
        (realPowerTwist (F.canonicalTopologicalData.determinantNorm t) x σ) π P := by
  have h := isPadicRankLPolynomial_realPowerTwist_move (ψ := ψ) (ν := ν) σ π 0 x P
  rw [realPowerTwist_zero, zero_add] at h
  rw [isPadicRankLPolynomial_comm, h]

end Rank

/-- JPSS 1983, Proposition (8.1)(i), in either rank order: irreducible
supercuspidal representations of different ranks have L-factor `1`. Their
Whittaker type comes from the supercuspidal Kirillov theorem. -/
theorem isPadicRankLPolynomial_one_of_supercuspidal {F : PadicField.{uF} p}
    {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {a b : ℕ} (hab : a ≠ b) {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (b + 1) F.Carrier) W}
    (hπ : Representation.IsIrreducible π)
    (hπs : letI := F.canonicalTopologicalData.topology; GeneralLinear.IsSupercuspidal π)
    (hσ : Representation.IsIrreducible σ)
    (hσs : letI := F.canonicalTopologicalData.topology; GeneralLinear.IsSupercuspidal σ) :
    IsPadicRankLPolynomial F ψ ν.val π σ 1 := by
  let := F.canonicalTopologicalData.topology
  rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
  · exact (isPadicSymmetricLPolynomial_of_lt hlt).mpr
      (supercuspidalUnequalRankLFactor p F ψ ν b a σ π hσ hσs
        (isOfWhittakerType_of_supercuspidalKirillov supercuspidalKirillov hπs hπ) hlt)
  · exact (isPadicSymmetricLPolynomial_of_le hlt.le).mpr
      (supercuspidalUnequalRankLFactor p F ψ ν a b π σ hπ hπs
        (isOfWhittakerType_of_supercuspidalKirillov supercuspidalKirillov hσs hσ) hlt)

section Seed

variable (F : PadicField.{uF} p) {a : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The seed `ν^(m/2) ρ` whose JPSS centered blocks `ν^(m/2 - i) ν^(m/2) ρ`,
`i = 0, …, m`, are the decreasing segment `ν^m ρ, …, νρ, ρ`. -/
def segmentCenteredSeed (m : ℕ)
    (ρ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V) :
    Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V :=
  realPowerTwist (F.canonicalTopologicalData.determinantNorm (a + 1)) ((m : ℝ) / 2) ρ

/-- The centered block `i` of the seed `ν^(m/2) ρ` is `ν^(m-i) ρ`, the block `i`
of the decreasing segment induction. -/
theorem centeredSegmentBlocks_segmentCenteredSeed (m : ℕ)
    (ρ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V) (i : Fin (m + 1)) :
    centeredSegmentBlocks F m (segmentCenteredSeed F m ρ) i =
      realPowerTwist (F.canonicalTopologicalData.determinantNorm (a + 1))
        ((m + 1 - 1 - (i : ℕ) : ℕ) : ℝ) ρ := by
  have hi : (i : ℕ) ≤ m := Nat.lt_succ_iff.mp i.isLt
  simp only [centeredSegmentBlocks, segmentCenteredSeed]
  rw [← realPowerTwist_add, Nat.add_sub_cancel, Nat.cast_sub hi]
  congr 1
  ring

theorem isIrreducible_segmentCenteredSeed (m : ℕ)
    {ρ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V}
    (hρ : Representation.IsIrreducible ρ) :
    Representation.IsIrreducible (segmentCenteredSeed F m ρ) :=
  (isIrreducible_twist_iff _ ρ).mpr hρ

theorem isSupercuspidal_segmentCenteredSeed (m : ℕ)
    {ρ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V}
    (hρ : letI := F.canonicalTopologicalData.topology; GeneralLinear.IsSupercuspidal ρ) :
    letI := F.canonicalTopologicalData.topology
    GeneralLinear.IsSupercuspidal (segmentCenteredSeed F m ρ) :=
  (isSupercuspidal_realPowerTwist_iff (a + 1) _ ρ).mpr hρ

set_option maxHeartbeats 1000000 in
/-- A component of the decreasing segment induction `i(ν^m A, …, νA, A)` on
`GL_((m+1)(a+1))(F)` is a component of JPSS's centered induction of the seed
`ν^(m/2) A`, whose blocks are the same. The heartbeat bound covers the
unification of the two block shapes and block families. -/
theorem isIrreducibleComponent_centered_of_segmentInducedDown {m : ℕ}
    (A : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, uV} ℂ (Langlands.GeneralLinear (a + 1) F.Carrier))
    {X : Type uW} [AddCommGroup X] [Module ℂ X]
    (π : Representation ℂ (Langlands.GeneralLinear ((m + 1) * a + m + 1) F.Carrier) X)
    (hr : ∑ _i : Fin (m + 1), (a + 1) = (m + 1) * a + m + 1)
    (h : letI := F.canonicalTopologicalData.topology
      IsIrreducibleComponent
        (F.canonicalTopologicalData.segmentInducedDown A (m + 1) (Nat.succ_pos a)).representation
        π) :
    letI := F.canonicalTopologicalData.topology
    IsIrreducibleComponent
      (F.canonicalNormalizedProductInduced (succBlockShape (fun _ => a) hr)
        (centeredSegmentBlocks F m (segmentCenteredSeed F m A.representation))) π := by
  let := F.canonicalTopologicalData.topology
  have hfac : (fun i => (F.canonicalTopologicalData.segmentFactorsDown A (m + 1)
        (Nat.succ_pos a) i).representation) =
      fun i : Fin (m + 1) => realPowerTwist (F.canonicalTopologicalData.determinantNorm (a + 1))
        ((m + 1 - 1 - (i : ℕ) : ℕ) : ℝ) A.representation :=
    funext fun i => rfl
  have h1 : IsIrreducibleComponent
      (F.canonicalTopologicalData.normalizedProductInduced
        (GeneralLinear.BlockShape.uniform (m + 1) (a + 1) (Nat.succ_pos a))
        (fun i => (F.canonicalTopologicalData.segmentFactorsDown A (m + 1)
          (Nat.succ_pos a) i).representation)) π := h
  rw [hfac] at h1
  have hb : centeredSegmentBlocks F m (segmentCenteredSeed F m A.representation) =
      fun i : Fin (m + 1) => realPowerTwist (F.canonicalTopologicalData.determinantNorm (a + 1))
        ((m + 1 - 1 - (i : ℕ) : ℕ) : ℝ) A.representation :=
    funext (centeredSegmentBlocks_segmentCenteredSeed F m A.representation)
  rw [hb]
  exact h1

end Seed

/-- A segment head is an irreducible component of the decreasing induction of
any representative of its beginning: it is the strong socle there. -/
theorem isIrreducibleComponent_segmentInducedDown_of_isSegmentHead {F : PadicField.{uF} p}
    {Δ : F.canonicalTopologicalData.Segment.{uV, uF}}
    {π : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear Δ.degree F.Carrier)}
    (hπ : F.canonicalTopologicalData.IsSegmentHead Δ π)
    (A : letI := F.canonicalTopologicalData.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank))
    (hA : Δ.base.IsRepresentedBy A) :
    letI := F.canonicalTopologicalData.topology
    IsIrreducibleComponent
      (F.canonicalTopologicalData.segmentInducedDown A.obj Δ.length Δ.rank_pos).representation
      π.representation := by
  obtain ⟨hirr, j, hj, -⟩ := hπ.isIrreducibleSocle_down A hA
  exact isIrreducibleComponent_of_injective hirr j hj

/-- `SegmentHeadLFactorStatement` for one pair of segments with
`deg Δ' ≤ deg Δ`, from JPSS 1983, Theorem (8.2) applied to the seeds
`ν^(m/2) A` and `ν^(k/2) A'` of the two segments. -/
theorem segmentHeadLFactor_of_degree_le
    (H : SquareIntegrableLFactorStatement.{uF, uV, uW, max uF uV, max uF uW})
    {F : PadicField.{uF} p}
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (Δ : F.canonicalTopologicalData.Segment.{uV, uF})
    (Δ' : F.canonicalTopologicalData.Segment.{uW, uF})
    (π : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear Δ.degree F.Carrier))
    (σ : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uW} ℂ (Langlands.GeneralLinear Δ'.degree F.Carrier))
    (A : letI := F.canonicalTopologicalData.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank))
    (A' : letI := F.canonicalTopologicalData.topology
      GeneralLinear.SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := Δ'.rank))
    (hπ : F.canonicalTopologicalData.IsSegmentHead Δ π)
    (hσ : F.canonicalTopologicalData.IsSegmentHead Δ' σ)
    (hA : Δ.base.IsRepresentedBy A) (hA' : Δ'.base.IsRepresentedBy A')
    (hle : Δ'.degree ≤ Δ.degree) :
    letI := F.canonicalTopologicalData.topology
    ∃ (P : ℂ[X]) (Q : Fin (min Δ.length Δ'.length) → ℂ[X]),
      IsPadicRankLPolynomial F ψ ν.val π.representation σ.representation P ∧
      (∀ j : Fin (min Δ.length Δ'.length), IsPadicRankLPolynomial F ψ ν.val
        (realPowerTwist (F.canonicalTopologicalData.determinantNorm Δ.rank)
          ((Δ.length : ℝ) + Δ'.length - 2 - (j : ℕ)) A.obj.representation)
        A'.obj.representation (Q j)) ∧
      P = ∏ j, Q j := by
  let := F.canonicalTopologicalData.topology
  have hπe := Classification.segmentSpecialEssentialSquareIntegrability.{uF, uV} F
    F.canonicalTopologicalData Δ.universeLift π
    ((isSegmentHead_universeLift_iff Δ π).mpr hπ).isSegmentQuotient
  have hσe := Classification.segmentSpecialEssentialSquareIntegrability.{uF, uW} F
    F.canonicalTopologicalData Δ'.universeLift σ
    ((isSegmentHead_universeLift_iff Δ' σ).mpr hσ).isSegmentQuotient
  have hπc := isIrreducibleComponent_segmentInducedDown_of_isSegmentHead hπ A hA
  have hσc := isIrreducibleComponent_segmentInducedDown_of_isSegmentHead hσ A' hA'
  obtain ⟨hAi, hAs⟩ := A.property
  obtain ⟨hA'i, hA's⟩ := A'.property
  clear hπ hσ hA hA'
  obtain ⟨⟨d, hd, cls⟩, n, hn⟩ := Δ
  obtain ⟨⟨d', hd', cls'⟩, n', hn'⟩ := Δ'
  obtain ⟨a, rfl⟩ : ∃ a, d = a + 1 := ⟨d - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, d' = b + 1 := ⟨d' - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, n' = k + 1 := ⟨n' - 1, by omega⟩
  have hr : ∑ _i : Fin (m + 1), (a + 1) = (m + 1) * a + m + 1 := by simp; ring
  have ht : ∑ _j : Fin (k + 1), (b + 1) = (k + 1) * b + k + 1 := by simp; ring
  have htr : (k + 1) * b + k ≤ (m + 1) * a + m := Nat.le_of_succ_le_succ hle
  obtain ⟨P, Q', hP, hQ', hPQ⟩ := H p F ψ ν a m ((m + 1) * a + m) b k ((k + 1) * b + k) hr ht
    (segmentCenteredSeed F m (a := a) A.obj.representation)
    (segmentCenteredSeed F k (a := b) A'.obj.representation)
    π.representation σ.representation
    (isIrreducible_segmentCenteredSeed F m hAi) (isSupercuspidal_segmentCenteredSeed F m hAs)
    (isIrreducible_segmentCenteredSeed F k hA'i) (isSupercuspidal_segmentCenteredSeed F k hA's)
    hπe (isIrreducibleComponent_centered_of_segmentInducedDown F (a := a) A.obj
      π.representation hr hπc)
    hσe (isIrreducibleComponent_centered_of_segmentInducedDown F (a := b) A'.obj
      σ.representation ht hσc)
    htr
  have hPr : IsPadicRankLPolynomial F ψ ν.val π.representation σ.representation P :=
    (isPadicRankLPolynomial_succ (r := (m + 1) * a + m) (k := (k + 1) * b + k)).mpr
      ((isPadicSymmetricLPolynomial_of_le htr).mpr hP)
  rcases eq_or_ne a b with rfl | hab
  · have hkm : k ≤ m := (le_iff_of_centeredSegment_rank hr ht).mp htr
    have hmin : min (m + 1) (k + 1) = k + 1 := min_eq_right (by omega)
    refine ⟨P, fun j => Q' (Fin.cast hmin j), hPr, fun j => ?_, ?_⟩
    · have hj : (j : ℕ) ≤ k := by
        have := j.isLt
        dsimp only at this
        omega
      have hq := (isPadicRankLPolynomial_succ (r := a) (k := a)).mpr (hQ' (Fin.cast hmin j))
      rw [centeredSegmentBlocks_segmentCenteredSeed, centeredSegmentBlocks_segmentCenteredSeed,
        isPadicRankLPolynomial_realPowerTwist_move] at hq
      have hx : (((m + 1 - 1 - ((0 : Fin (m + 1)) : ℕ) : ℕ) : ℝ) +
          ((k + 1 - 1 - ((Fin.cast hmin j : Fin (k + 1)) : ℕ) : ℕ) : ℝ)) =
          ((m + 1 : ℕ) : ℝ) + ((k + 1 : ℕ) : ℝ) - 2 - ((j : ℕ) : ℝ) := by
        simp only [Fin.val_cast, Fin.val_zero, Nat.add_sub_cancel, Nat.sub_zero,
          Nat.cast_sub hj]
        push_cast
        ring
      rw [hx] at hq
      exact hq
    · rw [hPQ]
      exact (Fin.prod_congr' Q' hmin).symm
  · have hone : ∀ j, Q' j = 1 := fun j =>
      IsPadicRankLPolynomial.unique
        ((isPadicRankLPolynomial_succ (r := a) (k := b)).mpr (hQ' j))
        (isPadicRankLPolynomial_one_of_supercuspidal ν hab
          (isIrreducible_centeredSegmentBlocks m
            (isIrreducible_segmentCenteredSeed F m hAi) 0)
          (isSupercuspidal_centeredSegmentBlocks m
            (isSupercuspidal_segmentCenteredSeed F m hAs) 0)
          (isIrreducible_centeredSegmentBlocks k
            (isIrreducible_segmentCenteredSeed F k hA'i) j)
          (isSupercuspidal_centeredSegmentBlocks k
            (isSupercuspidal_segmentCenteredSeed F k hA's) j))
    refine ⟨P, fun _ => 1, hPr, fun j => ?_, ?_⟩
    · exact isPadicRankLPolynomial_one_of_supercuspidal (a := a) (b := b) ν hab
        ((isIrreducible_twist_iff _ _).mpr hAi)
        ((isSupercuspidal_realPowerTwist_iff (a + 1) _ _).mpr hAs) hA'i hA's
    · rw [hPQ, Finset.prod_congr rfl fun j _ => hone j]
      simp

/-- Henniart 2002, §2.6, first display (`SegmentHeadLFactorStatement`), from
JPSS 1983, Theorem (8.2) (`SquareIntegrableLFactorStatement`) at the two
universe orders: the pair is ordered so that the second segment has the smaller
degree, and the result is transported back through the symmetry of the
L-polynomial relation. -/
theorem segmentHeadLFactor_of_squareIntegrable
    (H : SquareIntegrableLFactorStatement.{uF, uV, uW, max uF uV, max uF uW})
    (H' : SquareIntegrableLFactorStatement.{uF, uW, uV, max uF uW, max uF uV}) :
    SegmentHeadLFactorStatement.{uF, uV, uW} := by
  intro p _ F ψ ν Δ Δ' π σ A A' hπ hσ hA hA'
  by_cases hle : Δ'.degree ≤ Δ.degree
  · exact segmentHeadLFactor_of_degree_le H ψ ν Δ Δ' π σ A A' hπ hσ hA hA' hle
  · obtain ⟨P, Q, hP, hQ, hPQ⟩ := segmentHeadLFactor_of_degree_le H' ψ ν Δ' Δ σ π A' A
      hσ hπ hA' hA (le_of_not_ge hle)
    have hmin : min Δ.length Δ'.length = min Δ'.length Δ.length := min_comm _ _
    refine ⟨P, fun j => Q (Fin.cast hmin j), (isPadicRankLPolynomial_comm _ _ _).mp hP,
      fun j => ?_, ?_⟩
    · have hq := (isPadicRankLPolynomial_realPowerTwist_comm _ _ _ _).mp (hQ (Fin.cast hmin j))
      rw [Fin.val_cast, add_comm (Δ'.length : ℝ)] at hq
      exact hq
    · rw [hPQ]
      exact (Fin.prod_congr' Q hmin).symm

end Langlands.RankinSelberg
