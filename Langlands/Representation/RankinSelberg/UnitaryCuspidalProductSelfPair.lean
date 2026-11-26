import Langlands.Representation.RankinSelberg.UnitarySupercuspidalBaseFamily
import Langlands.Representation.RankinSelberg.SupercuspidalPairPoleOrder
import Langlands.Representation.RankinSelberg.SupercuspidalEqualRankLFactorProof
import Langlands.Representation.RankinSelberg.TemperedLFactorProof
import Langlands.Representation.RankinSelberg.GroupedLFactorReduction
import Langlands.Representation.RankinSelberg.BlockShapeSmoothDualGamma
import Langlands.Representation.RankinSelberg.SegmentPairPoleOrder
import Langlands.Representation.Classification.UnitarySupercuspidalInductionTempered
import Langlands.Representation.Classification.TwistedProductOrdinaryDualProof

/-! # The self-pair Euler denominator of a product of distinct unitary supercuspidals -/

noncomputable section

namespace Langlands.RankinSelberg

open Classification GeneralLinear HarmonicAnalysis LocalFactor Polynomial

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance unitaryProductSelfPairTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance unitaryProductSelfPairGroupTopology (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup n

set_option maxHeartbeats 2200000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- The certified self-pair denominator of a normalized product of distinct
unitarizable supercuspidals of equal positive rank has order the number of
factors at `1` and is nonzero at the residue cardinality. -/
theorem unitaryCuspidalProduct_selfPair {s r : ℕ} (hs : 0 < s)
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (C : Fin s → SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := r + 1))
    (hU : ∀ i, IsUnitarizable (C i).obj.representation)
    (hDistinct : Pairwise fun i j => IsEmpty ((C i).obj.representation.Equiv (C j).obj.representation)) :
    let P := F.canonicalTopologicalData.normalizedProductInduced (BlockShape.uniform s (r + 1) (Nat.succ_pos r))
      (fun i => (C i).obj.representation)
    ∃ Q : ℂ[X], IsPadicRankLPolynomial F ψ ν.val P (smoothContragredient P) Q ∧
      Q.eval (F.canonicalTopologicalData.residueCardinality : ℂ) ≠ 0 ∧
      lPolynomialPoleOrderAtZero Q = s := by
  classical
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
  let T := F.canonicalTopologicalData
  let B := BlockShape.uniform (s + 1) (r + 1) (Nat.succ_pos r)
  let ρ (i : Fin (s + 1)) := (C i).obj.representation
  let Cd (j : Fin (s + 1)) : SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := r + 1) :=
    ⟨(C j).obj.contragredient,
      ((C j).obj.isIrreducible_contragredient_iff (compactOpen_cofinal F T (r + 1))
        (C j).property.2.1).mpr (C j).property.1,
      isSupercuspidal_smoothContragredient F T (r + 1) (C j).obj (ρ j) (C j).property.2⟩
  let ρd (j : Fin (s + 1)) := (Cd j).obj.representation
  have hAd (j : Fin (s + 1)) := (C j).property.2.1
  have hUd (j : Fin (s + 1)) : IsUnitarizable (ρd j) :=
    HarishChandraSchwartz.isUnitarizable_smoothContragredient_of_admissible
      (compactOpen_cofinal F T (r + 1)) (hAd j) (hU j)
  obtain ⟨Q, L, hQ, hL, hQL⟩ := TemperedLFactorStatement.blockShape F ψ ν temperedLFactor B B ρ ρd
    (fun i => (C i).property.1)
    (fun i => unitarizableSupercuspidal_isSquareIntegrable F (Nat.succ_pos r) (C i) (hU i))
    (fun j => (Cd j).property.1)
    (fun j => unitarizableSupercuspidal_isSquareIntegrable F (Nat.succ_pos r) (Cd j) (hUd j))
  let e := T.normalizedProductSmoothDualEquiv B ρ hAd
  let D (i j : Fin (s + 1)) := unitarySupercuspidalDualPairEuler supercuspidalEqualRankLFactor ψ ν (ρ i) (ρ j)
    (C i).property.1 (C j).property.1 (C i).property.2 (C j).property.2 (hU i) (hU j)
  have hpoly (i j : Fin (s + 1)) : L i j = (D i j).data.polynomial :=
    (hL i j).unique (isPadicRankLPolynomial_succ.mpr (D i j).certified)
  refine ⟨Q, ?_, ?_, ?_⟩
  · let P := T.normalizedProductInduced B ρ
    change IsPadicSymmetricLPolynomial F ψ ν.val P (smoothContragredient P) Q
    exact (IsPadicSymmetricLPolynomial.congr_equiv (Representation.Equiv.refl P) e).mpr hQ
  · rw [hQL, eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    rw [eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    rw [hpoly i j]
    have h := (D i j).data.denominator_ne_zero (s := -1) (by simp)
    rw [(D i j).data.denominator_eq_eval] at h
    have harg : spectralParameter (D i j).data.q
        (lt_trans zero_lt_one (D i j).data.q_gt_one) (-1) = (T.residueCardinality : ℂ) := by
      have hq : (T.residueCardinality : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
        (lt_trans Nat.zero_lt_one T.residueCardinality_gt_one).ne'
      simp [spectralParameter, (D i j).q_eq, T, Complex.exp_log hq]
    rw [harg] at h
    exact h
  · have hparam (i j : Fin (s + 1)) : (1 : ℂ) ∈ (D i j).data.parameters ↔ i = j := by
      constructor
      · intro h
        obtain ⟨_, ⟨e'⟩⟩ := (D i j).one_mem_iff.mp h
        have eb := ((smoothAdmissibleDuality (compactOpen_cofinal F T (r + 1))).2 (ρ j) (hAd j)).2
        by_contra! hij
        exact (hDistinct hij).false (e'.trans ((smoothBidual (hAd j).1).ofBijective eb).symm)
      · rintro rfl
        exact (D i i).one_mem_iff.mpr
          (isRankContragredient_dual_of_equiv (ρ i) (ρ i) (hAd i) rfl ⟨Representation.Equiv.refl _⟩)
    have horder (i j : Fin (s + 1)) : lPolynomialPoleOrderAtZero (L i j) = if i = j then 1 else 0 := by
      rw [hpoly, FiniteUnitaryEuler.polynomial, lPolynomialPoleOrderAtZero_prod_one_sub_C_mul_X]
      simp only [hparam]
    rw [hQL, lPolynomialPoleOrderAtZero_prod_prod L (fun i j => (hL i j).coeff_zero)]
    change (∑ i : Fin (s + 1), ∑ j : Fin (s + 1), lPolynomialPoleOrderAtZero (L i j)) = s + 1
    simp only [horder]
    calc
      _ = ∑ _i : Fin (s + 1), (1 : ℕ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj
          simp [Ne.symm hj]
        · simp
      _ = _ := by simp

end Langlands.RankinSelberg
