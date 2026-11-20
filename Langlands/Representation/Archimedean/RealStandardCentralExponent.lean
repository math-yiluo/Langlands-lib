import Langlands.Representation.Archimedean.RealBlockLeftDerivative
import Langlands.Representation.Archimedean.RealBlockPositionData
import Langlands.Representation.Archimedean.RealPrincipalSeriesDualityProof
import Langlands.Representation.Archimedean.RealRankZeroStandardModule
import Langlands.Representation.Archimedean.RealStandardNontrivialProof
import Langlands.Representation.Archimedean.UnitaryGenericPairRegularityStatement

/-! # The central exponent of a real standard module -/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean
open GramFormula PrincipalSeriesExtension RealBlockDerivative RealBlockPosition
open RealPrincipalSeriesDuality

/-- The scalar for the central Lie action, given by the sum of the complex position exponents. -/
def realStandardCentralExponent (n : ℕ) (ds : List RealBlock) : ℂ :=
  ∑ i : Fin n, realPositionExponent ds i

private theorem sum_normalization_shift (n : ℕ) :
    (∑ i : Fin n, (((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ))) = 0 := by
  have h := sum_modulusExponent (n := n) (fun _ => 1)
  simp only [Complex.ofReal_one, mul_one, sub_self, Complex.ofReal_zero, ite_self,
    Finset.sum_const_zero] at h
  calc
    _ = (∑ i : Fin n, modulusExponent n i) / 2 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by unfold modulusExponent; ring
    _ = 0 := by rw [h, zero_div]

/-- The scalar matrix `I` acts by the sum of the unshifted position exponents. -/
theorem realStandardLie_identity (n : ℕ) (ds : List RealBlock)
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) :
    realStandardLie n ds (1 ⊗ₜ (1 : Matrix (Fin n) (Fin n) ℝ)) f =
      realStandardCentralExponent n ds • f := by
  have hf : (f : Langlands.GeneralLinear n ℝ → ℂ) ∈
      principalSeries ℝ n (realPositionCharacter ds) := f.2.1.1
  have hexp := isExpEquivariant_of_mem_principalSeries
    (fun i x => realPositionCharacter_exp ds i x) hf
  apply Subtype.ext
  funext g
  rw [realStandardLie_one_tmul_apply_coe, rightDerivative_eq_fderiv hf.1, mul_one]
  have h := fderiv_upperTriangular_of_isExpEquivariant hf.1 hexp g
    (Matrix.blockTriangular_one : (1 : Matrix (Fin n) (Fin n) ℝ).IsUpperTriangular)
  simp only [one_mul, Matrix.one_apply_eq, Complex.ofReal_one, mul_one] at h
  rw [show (∑ i : Fin n, (realPositionExponent ds i + ((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ))) =
      (∑ i : Fin n, realPositionExponent ds i) from by
    simp only [add_sub_assoc, Finset.sum_add_distrib, sum_normalization_shift, add_zero]] at h
  exact h

private theorem re_sum_positionExponent : ∀ ds : List RealBlock,
    (∑ i : Fin (realRank ds), realPositionExponent ds i).re =
      (ds.map fun d => (d.rank : ℝ) * realBlockExponent d).sum
  | [] => by simp [realPositionExponent]
  | .character d :: ds => by
      rw [realRank_cons, RealBlock.rank, Nat.one_add, Fin.sum_univ_succ]
      simp only [Complex.add_re, Fin.val_zero, Fin.val_succ, realPositionExponent,
        re_sum_positionExponent ds, List.map_cons, List.sum_cons, RealBlock.rank,
        realBlockExponent, Nat.cast_one, one_mul]
  | .induced d :: ds => by
      rw [realRank_cons, RealBlock.rank, show 2 + realRank ds = (realRank ds).succ.succ by omega,
        Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp only [Complex.add_re, Fin.val_zero, Fin.val_succ, realPositionExponent,
        Complex.sub_re, re_sum_positionExponent ds, List.map_cons, List.sum_cons,
        RealBlock.rank, realBlockExponent, Nat.cast_ofNat]
      ring

/-- Infinitesimal unitarity forces the rank-weighted sum of the block exponents to vanish. -/
theorem realStandard_weightedExponent_eq_zero {n : ℕ} {ds : List RealBlock}
    (hrank : realRank ds = n)
    (hunit : IsRealUnitarizableGKModule n (realStandardRep n ds) (realStandardLie n ds)) :
    (ds.map fun d => (d.rank : ℝ) * realBlockExponent d).sum = 0 := by
  let hnt := realStandardNontrivial n ds hrank
  obtain ⟨f, hf⟩ := exists_ne (0 : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
  obtain ⟨b, hb⟩ := hunit
  let c := realStandardCentralExponent n ds
  have hright : b.inner f (c • f) = c * b.inner f f := calc
    _ = starRingEnd ℂ (b.inner (c • f) f) := (b.conj_inner_symm f _).symm
    _ = _ := by rw [b.smul_left, map_mul, Complex.conj_conj, b.conj_inner_symm]
  have h := hb (1 : Matrix (Fin n) (Fin n) ℝ) f f
  rw [realStandardLie_identity] at h
  change b.inner (c • f) f + b.inner f (c • f) = 0 at h
  rw [b.smul_left, hright, ← add_mul] at h
  have hc := (mul_eq_zero.mp h).resolve_right fun hzero => hf (b.definite f hzero)
  have hre := congrArg Complex.re hc
  simp only [Complex.add_re, Complex.conj_re, Complex.zero_re] at hre
  have hc' : c.re = 0 := by linarith
  rw [← re_sum_positionExponent, hrank]
  exact hc'

private theorem weightedExponent_eq_rank_mul (r : ℝ) (ds : List RealBlock)
    (he : ∀ d ∈ ds, realBlockExponent d = r) :
    (ds.map fun d => (d.rank : ℝ) * realBlockExponent d).sum = (realRank ds : ℝ) * r := by
  induction ds with
  | nil => simp
  | cons a ds ih =>
    rw [List.map_cons, List.sum_cons, realRank_cons, Nat.cast_add, add_mul, he a (by simp),
      ih (fun d hd => he d (List.mem_cons_of_mem a hd))]

/-- A unitarizable standard module whose blocks have a common real exponent has exponent zero. -/
theorem realStandard_exponent_eq_zero_of_tied {n : ℕ} {ds : List RealBlock} {r : ℝ}
    (hrank : realRank ds = n)
    (hunit : IsRealUnitarizableGKModule n (realStandardRep n ds) (realStandardLie n ds))
    (he : ∀ d ∈ ds, realBlockExponent d = r) :
    ∀ d ∈ ds, realBlockExponent d = 0 := by
  intro d hd
  have h := realStandard_weightedExponent_eq_zero hrank hunit
  rw [weightedExponent_eq_rank_mul r ds he] at h
  rcases mul_eq_zero.mp h with hzero | hr
  · have hds := RealRankZeroStandardModule.eq_nil_of_realRank_eq_zero ds (Nat.cast_eq_zero.mp hzero)
    simp [hds] at hd
  · exact (he d hd).trans hr

end Langlands.Archimedean
