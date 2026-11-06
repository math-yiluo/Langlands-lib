import Langlands.Representation.RankinSelberg.SupercuspidalPairPoleOrder
import Langlands.Representation.RankinSelberg.SegmentFactorStatement
import Langlands.Representation.RankinSelberg.PadicPairLPolynomialNormalization
import Langlands.Representation.RankinSelberg.PoleOrderSegmentCombinatorics
import Langlands.Representation.Classification.CuspidalProductContragredient
import Langlands.Representation.Classification.SegmentHeadContragredient
import Langlands.Representation.Classification.UnlinkedCuspidalContentInjectivityProof
import Langlands.Representation.Classification.SegmentHeadSupportSplit

/-!
# Pole orders at `s = 0` of pairs of segment representations

The contragredient segment `Δ^∨ = [ρ̃', ν^(m-1) ρ̃'] = [ν^(1-m) ρ̃, ρ̃]` of
`Δ = [ρ, ρ']`, `ρ' = ν^(m-1) ρ`, and the order of the pole at `s = 0` of
`L(s, St(Δ) × St(Δ'))`: it is `1` if the segment `Δ'^∨` begins in `Δ` and `Δ` ends
in `Δ'^∨` (`SegmentPoleLink Δ Δ'^∨`), and `0` otherwise. The computation assumes Henniart 2002, §2.6
(`SegmentHeadLFactorStatement`), JPSS 1983, Proposition (8.1), and that irreducible
supercuspidal representations are of Whittaker type.
-/

noncomputable section

open CategoryTheory

namespace Langlands

universe uF uV uW

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

namespace Segment

open Classification.CuspidalProductContragredient

theorem dual_base (Δ : Segment.{uV, uF} T) : Δ.dual.base = dualDatum Δ.last := rfl

/-- `(ν^i ρ)~ = ν^(-i) ρ̃`. -/
theorem dualDatum_member (Δ : Segment.{uV, uF} T) (i : ℕ) :
    dualDatum (Δ.member i) = (dualDatum Δ.base).twist (-(i : ℝ)) := by
  rw [member, dualDatum_twist]

theorem member_dual (Δ : Segment.{uV, uF} T) (i : ℕ) :
    Δ.dual.member i = (dualDatum Δ.base).twist ((i : ℝ) - ((Δ.length - 1 : ℕ) : ℝ)) := by
  rw [member, dual_base, last, dualDatum_member, CuspidalDatum.twist_twist]
  congr 1

/-- The member `i` of `Δ^∨` is the contragredient of the member `m - 1 - i` of `Δ`. -/
theorem member_dual_of_lt (Δ : Segment.{uV, uF} T) {i : ℕ} (hi : i < Δ.length) :
    Δ.dual.member i = dualDatum (Δ.member (Δ.length - 1 - i)) :=
  Δ.dual_member i hi

theorem mem_support_dual_iff (Δ : Segment.{uV, uF} T) (ρ : CuspidalDatum.{uV, uF} T) :
    ρ ∈ Δ.dual.support ↔ dualDatum ρ ∈ Δ.support := by
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hi' : i < Δ.length := hi
    refine ⟨Δ.length - 1 - i, by omega, ?_⟩
    rw [member_dual_of_lt Δ hi', dualDatum_dualDatum]
  · rintro ⟨i, hi, h⟩
    refine ⟨Δ.length - 1 - i, by simp only [dual_length]; omega, ?_⟩
    rw [member_dual_of_lt Δ (by omega), show Δ.length - 1 - (Δ.length - 1 - i) = i by omega,
      h, dualDatum_dualDatum]

end Segment

end PadicField.TopologicalData

namespace RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial
open PadicField.TopologicalData Classification.CuspidalProductContragredient

variable {p : ℕ} [Fact p.Prime]

section Combinatorics

variable {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- A sum of indicators of pairwise exclusive conditions is the indicator of their
disjunction. -/
theorem sum_ite_eq_ite_exists {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P]
    (h : ∀ i j, P i → P j → i = j) [Decidable (∃ i, P i)] :
    (∑ i, if P i then 1 else 0 : ℕ) = if ∃ i, P i then 1 else 0 := by
  split_ifs with hex
  · obtain ⟨i, hi⟩ := hex
    rw [Finset.sum_eq_single i (fun j _ hj => if_neg fun hj' => hj (h j i hj' hi))
      (fun hi' => absurd (Finset.mem_univ i) hi'), if_pos hi]
  · push_neg at hex
    simp [hex]

/-- With `n = len Δ` and `n' = len Δ'`, some `ν^(n+n'-2-j) ρ`, `j < min(n, n')`, with `ρ`
the beginning of `Δ`, is the contragredient of the beginning of `Δ'` exactly when
`Δ'^∨` begins in `Δ` and `Δ` ends in `Δ'^∨`. -/
theorem exists_twist_eq_dualDatum_iff_segmentPoleLink (Δ Δ' : Segment.{uV, uF} T) :
    (∃ j : Fin (min Δ.length Δ'.length),
        Δ.base.twist (((Δ.length : ℤ) + Δ'.length - 2 - (j : ℕ) : ℤ) : ℝ) =
          dualDatum Δ'.base) ↔
      SegmentPoleLink Δ Δ'.dual := by
  have hfree := Classification.cuspidalIntegralTwistFreeness.{uF, uV} F T
  have hΔ := Δ.hasIntegralCoordinates_self
  have hn := Δ.length_pos
  have hn' := Δ'.length_pos
  -- If `ρ̃'_0 = ν^c ρ`, then `Δ'^∨` has integral coordinates `[c - n' + 1, c]` over `ρ`.
  have hcoord : ∀ c : ℤ, dualDatum Δ'.base = Δ.base.twist (c : ℝ) →
      Δ'.dual.HasIntegralCoordinates Δ.base (c - Δ'.length + 1) c := by
    intro c hc
    refine ⟨?_, by simp only [Segment.dual_length]; ring⟩
    rw [Segment.dual_base, Segment.last, Segment.dualDatum_member, hc,
      CuspidalDatum.twist_twist, Nat.cast_sub (by omega : 1 ≤ Δ'.length)]
    congr 1
    push_cast
    ring
  have hlast : Δ.last = Δ.base.twist (((Δ.length : ℤ) - 1 : ℤ) : ℝ) := by
    rw [Segment.last, Segment.member, Nat.cast_sub (by omega : 1 ≤ Δ.length)]
    push_cast
    rfl
  constructor
  · rintro ⟨j, hj⟩
    have hjlt := j.isLt
    rw [Nat.lt_min] at hjlt
    have hD := hcoord _ hj.symm
    refine ⟨?_, ?_⟩
    · rw [hD.1, hΔ.twist_mem_support_iff hfree]
      omega
    · rw [hlast, hD.twist_mem_support_iff hfree]
      omega
  · rintro ⟨h1, h2⟩
    obtain ⟨i, hi, hi'⟩ := h1
    -- `ρ̃'_0 = ν^(n'-1) Δ'^∨_0 = ν^(i + n' - 1) ρ`.
    have hc : dualDatum Δ'.base = Δ.base.twist ((((i : ℕ) : ℤ) + Δ'.length - 1 : ℤ) : ℝ) := by
      rw [← Segment.dual_last, Segment.last, Segment.member, ← hi', Segment.member,
        CuspidalDatum.twist_twist, Segment.dual_length, Nat.cast_sub (by omega : 1 ≤ Δ'.length)]
      congr 1
      push_cast
      ring
    have hD := hcoord _ hc
    rw [hlast, hD.twist_mem_support_iff hfree] at h2
    refine ⟨⟨Δ.length - 1 - i, by rw [Nat.lt_min]; omega⟩, ?_⟩
    rw [hc]
    congr 2
    simp only
    omega

open Classical in
/-- The sum over `j < min(n, n')` of the indicators `[ν^(n+n'-2-j) ρ = ρ̃'_0]` is the
indicator of `SegmentPoleLink Δ Δ'^∨`, by integral twist freeness. -/
theorem sum_ite_twist_eq_dualDatum (Δ Δ' : Segment.{uV, uF} T) :
    (∑ j : Fin (min Δ.length Δ'.length),
        if Δ.base.twist ((Δ.length : ℝ) + Δ'.length - 2 - (j : ℕ)) = dualDatum Δ'.base
        then 1 else 0) =
      if SegmentPoleLink Δ Δ'.dual then 1 else 0 := by
  have hfree := Classification.cuspidalIntegralTwistFreeness.{uF, uV} F T
  have hcast : ∀ j : Fin (min Δ.length Δ'.length),
      ((Δ.length : ℝ) + Δ'.length - 2 - (j : ℕ)) =
        (((Δ.length : ℤ) + Δ'.length - 2 - (j : ℕ) : ℤ) : ℝ) := by
    intro j
    push_cast
    ring
  simp only [hcast]
  rw [sum_ite_eq_ite_exists, if_congr (exists_twist_eq_dualDatum_iff_segmentPoleLink Δ Δ')
    rfl rfl]
  intro j j' hj hj'
  have h := Δ.base.integralTwist_injective hfree (hj.trans hj'.symm)
  ext
  omega

end Combinatorics

section Factors

variable {F : PadicField.{uF} p}
  {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
  {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier}

/-- An L-polynomial of a pair of arbitrary ranks is nonzero. -/
theorem IsPadicRankLPolynomial.ne_zero {n t : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (Langlands.GeneralLinear n F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear t F.Carrier) W} {P : ℂ[X]}
    (h : IsPadicRankLPolynomial F ψ ν π σ P) : P ≠ 0 := by
  match n, t, π, σ, h with
  | _ + 1, _ + 1, _, _, h =>
    exact ne_zero_of_coeff_zero_eq_one
      (IsPadicSymmetricLPolynomial.coeff_zero (isPadicRankLPolynomial_succ.mp h))

/-- The L relation of a pair of arbitrary ranks is invariant under representation
equivalences. -/
theorem IsPadicRankLPolynomial.congr_equiv {n t : ℕ} {V : Type uV} {W : Type uW}
    {V₂ : Type*} {W₂ : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup W₂] [Module ℂ W₂]
    {π : Representation ℂ (Langlands.GeneralLinear n F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear t F.Carrier) W}
    {π₂ : Representation ℂ (Langlands.GeneralLinear n F.Carrier) V₂}
    {σ₂ : Representation ℂ (Langlands.GeneralLinear t F.Carrier) W₂}
    (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂) {P : ℂ[X]} :
    IsPadicRankLPolynomial F ψ ν π σ P ↔ IsPadicRankLPolynomial F ψ ν π₂ σ₂ P := by
  match n, t, π, σ, π₂, σ₂, φ, φ' with
  | _ + 1, _ + 1, _, _, _, _, φ, φ' => exact IsPadicSymmetricLPolynomial.congr_equiv φ φ'
  | 0, _, _, _, _, _, _, _ => exact Iff.rfl
  | _ + 1, 0, _, _, _, _, _, _ => exact Iff.rfl

end Factors

section Supercuspidal

variable {F : PadicField.{uF} p}

/-- Two supercuspidal objects `X` and `Y` satisfy `X ≅ Ỹ` exactly when the class of
`X` is that of the contragredient `Ỹ`. -/
theorem nonempty_equiv_smoothContragredient_iff {n : ℕ}
    (X Y : letI := F.canonicalTopologicalData.topology
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := n)) :
    letI := F.canonicalTopologicalData.topology
    haveI := F.canonicalTopologicalData.generalLinearTopologicalGroup n
    Nonempty (X.obj.representation.Equiv (smoothContragredient Y.obj.representation)) ↔
      X.isoClass = (dualRep F.canonicalTopologicalData Y).isoClass := by
  letI := F.canonicalTopologicalData.topology
  haveI := F.canonicalTopologicalData.generalLinearTopologicalGroup n
  rw [SupercuspidalRep.isoClass_eq_iff]
  constructor
  · rintro ⟨e⟩
    exact ⟨ObjectProperty.isoMk _ (SmoothRep.mkIso e)⟩
  · rintro ⟨e⟩
    exact ⟨SmoothRep.equivOfIso ((supercuspidalProperty (F := F.Carrier) (n := n)).ι.mapIso e)⟩

variable {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)

open Classical in
/-- JPSS 1983, Proposition (8.1), at `s = 0`, on cuspidal data: for representatives
`X` of `ρ` and `Y` of `ρ'`, `L(s, X × Y)` has a pole of order `1` at `s = 0` if
`ρ = ρ̃'`, and none otherwise. Both parts of (8.1) and the Whittaker type of the
supercuspidal representatives are hypotheses. -/
theorem lPolynomialPoleOrderAtZero_of_cuspidalData
    (h81 : SupercuspidalEqualRankLFactorStatement.{uF, uV, uV})
    (h81i : SupercuspidalUnequalRankLFactorStatement.{uF, uV, uV})
    (hW : ∀ (r : ℕ) (A : letI := F.canonicalTopologicalData.topology
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r + 1)),
      letI := F.canonicalTopologicalData.topology
      IsOfWhittakerType r (standardCharacter ψ r) A.obj.representation)
    (ρ ρ' : F.canonicalTopologicalData.CuspidalDatum.{uV, uF})
    (X : letI := F.canonicalTopologicalData.topology
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ.rank))
    (Y : letI := F.canonicalTopologicalData.topology
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ'.rank))
    (hX : ρ.IsRepresentedBy X) (hY : ρ'.IsRepresentedBy Y) {Q : ℂ[X]}
    (hQ : letI := F.canonicalTopologicalData.topology
      IsPadicRankLPolynomial F ψ ν.val X.obj.representation Y.obj.representation Q) :
    lPolynomialPoleOrderAtZero Q = if ρ = dualDatum ρ' then 1 else 0 := by
  letI := F.canonicalTopologicalData.topology
  have hone : lPolynomialPoleOrderAtZero (1 : ℂ[X]) = 0 := rootMultiplicity_eq_zero (by simp)
  obtain ⟨_ | a, ha, c⟩ := ρ
  · exact absurd ha (lt_irrefl 0)
  obtain ⟨_ | b, hb, c'⟩ := ρ'
  · exact absurd hb (lt_irrefl 0)
  have hrank : ∀ h : (⟨a + 1, ha, c⟩ : F.canonicalTopologicalData.CuspidalDatum.{uV, uF}) =
      dualDatum ⟨b + 1, hb, c'⟩, a = b := fun h => by
    have := congrArg CuspidalDatum.rank h
    simp only [dualDatum_rank] at this
    omega
  rcases Nat.lt_trichotomy a b with hab | rfl | hab
  · rw [if_neg fun h => hab.ne (hrank h)]
    have h1 := h81i p F ψ ν b a Y.obj.representation X.obj.representation Y.property.1
      Y.property.2 (hW a X) hab
    rw [((isPadicSymmetricLPolynomial_of_lt hab).mp hQ).unique h1, hone]
  · rw [lPolynomialPoleOrderAtZero_of_supercuspidalEqualRank h81 ν X.property.1 X.property.2
      Y.property.1 (hW a Y) ((isPadicSymmetricLPolynomial_of_le le_rfl).mp hQ),
      contragredientIndicator]
    refine if_congr ?_ rfl rfl
    rw [nonempty_equiv_smoothContragredient_iff X Y, show X.isoClass = c from hX,
      show (dualRep F.canonicalTopologicalData Y).isoClass =
        (dualDatum (⟨a + 1, hb, c'⟩ : F.canonicalTopologicalData.CuspidalDatum.{uV, uF})).cls
        from dualRep_represents hY]
    constructor
    · intro h
      exact congrArg (CuspidalDatum.mk (a + 1) ha) h
    · intro h
      simp only [dualDatum, CuspidalDatum.mk.injEq, heq_eq_eq, true_and] at h
      exact h
  · rw [if_neg fun h => hab.ne' (hrank h)]
    have h1 := h81i p F ψ ν a b X.obj.representation Y.obj.representation X.property.1
      X.property.2 (hW b Y) hab
    rw [((isPadicSymmetricLPolynomial_of_le hab.le).mp hQ).unique h1,
      hone]

open Classical in
/-- **Pole order at `s = 0` of a pair of segment representations.** Let `π = St(Δ)` and
`σ = St(Δ')` be irreducible heads of the inductions of the segments `Δ` and `Δ'`
(`IsSegmentHead`). Assuming Henniart 2002, §2.6 (`SegmentHeadLFactorStatement`),
JPSS 1983, Proposition (8.1), and the Whittaker type of irreducible supercuspidal
representations, the L-polynomial of `π × σ` has a root of multiplicity `1` at
`1` (a simple pole of `L(s, π × σ)` at `s = 0`) if `SegmentPoleLink Δ Δ'^∨`, and no
root at `1` otherwise. -/
theorem lPolynomialPoleOrderAtZero_of_segmentHeads
    (hSH : SegmentHeadLFactorStatement.{uF, uV, uV})
    (h81 : SupercuspidalEqualRankLFactorStatement.{uF, uV, uV})
    (h81i : SupercuspidalUnequalRankLFactorStatement.{uF, uV, uV})
    (hW : ∀ (r : ℕ) (A : letI := F.canonicalTopologicalData.topology
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r + 1)),
      letI := F.canonicalTopologicalData.topology
      IsOfWhittakerType r (standardCharacter ψ r) A.obj.representation)
    (Δ Δ' : F.canonicalTopologicalData.Segment.{uV, uF})
    (π : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear Δ.degree F.Carrier))
    (σ : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear Δ'.degree F.Carrier))
    (hπ : F.canonicalTopologicalData.IsSegmentHead Δ π)
    (hσ : F.canonicalTopologicalData.IsSegmentHead Δ' σ) {P : ℂ[X]}
    (hP : letI := F.canonicalTopologicalData.topology
      IsPadicRankLPolynomial F ψ ν.val π.representation σ.representation P) :
    lPolynomialPoleOrderAtZero P = if SegmentPoleLink Δ Δ'.dual then 1 else 0 := by
  letI := F.canonicalTopologicalData.topology
  obtain ⟨A, hA, -⟩ := id hπ
  obtain ⟨A', hA', -⟩ := id hσ
  obtain ⟨P₀, Q, hP₀, hQ, hPQ⟩ := hSH p F ψ ν Δ Δ' π σ A A' hπ hσ hA hA'
  rw [hP.unique hP₀, hPQ, lPolynomialPoleOrderAtZero_prod _ _ fun j _ => (hQ j).ne_zero,
    ← sum_ite_twist_eq_dualDatum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact lPolynomialPoleOrderAtZero_of_cuspidalData ν h81 h81i hW _ Δ'.base _ A'
    (Classification.SegmentHeadSupport.isRepresentedBy_twistRep F.canonicalTopologicalData _ hA)
    hA' (hQ j)

end Supercuspidal

end RankinSelberg

end Langlands
