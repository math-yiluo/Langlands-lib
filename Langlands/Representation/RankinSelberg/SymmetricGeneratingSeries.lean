import Langlands.Representation.Whittaker.Spherical
import Mathlib.Data.Finsupp.Multiset
import Mathlib.RingTheory.PowerSeries.WellKnown

/-! # Generating series for the complete symmetric polynomials -/

noncomputable section

namespace Langlands.GeneralLinear.Spherical

open MvPolynomial

variable (σ R : Type*) [Fintype σ] [DecidableEq σ] [CommRing R]

/-- The generating series of complete homogeneous symmetric polynomials. -/
def completeSeries : PowerSeries (MvPolynomial σ R) :=
  PowerSeries.mk (hsymm σ R)

private theorem prod_map_eq_prod_count (s : Multiset σ) :
    (s.map (X : σ → MvPolynomial σ R)).prod = ∏ i, X i ^ s.count i := by
  rw [Finset.prod_multiset_map_count]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  rw [Multiset.count_eq_zero_of_notMem (fun h => hi (Multiset.mem_toFinset.2 h)), pow_zero]

/-- Each variable contributes one geometric series. -/
theorem completeSeries_eq_prod :
    completeSeries σ R =
      ∏ i : σ, PowerSeries.mk (fun k : ℕ => (X i : MvPolynomial σ R) ^ k) := by
  apply PowerSeries.ext
  intro k
  rw [completeSeries, PowerSeries.coeff_mk, PowerSeries.coeff_prod]
  simp_rw [PowerSeries.coeff_mk]
  rw [hsymm]
  conv_rhs => rw [← Finset.sum_coe_sort]
  let e : Sym σ k ≃ ↥(Finset.finsuppAntidiag (Finset.univ : Finset σ) k) :=
    (Sym.equivNatSum σ k).trans (Equiv.subtypeEquivRight fun f => by
      simp [Finset.mem_finsuppAntidiag, Finsupp.sum_fintype, Function.id_def])
  apply Fintype.sum_equiv e
  intro s
  change (s.val.map X).prod = ∏ i, X i ^ (s.val.count i)
  exact prod_map_eq_prod_count σ R s.val

omit [Fintype σ] [DecidableEq σ] in
private theorem geometric_mul_linear (x : MvPolynomial σ R) :
    PowerSeries.mk (fun k : ℕ => x ^ k) *
      (1 - PowerSeries.C x * PowerSeries.X) = 1 := by
  have h := congrArg (PowerSeries.rescale x)
    (PowerSeries.mk_one_mul_one_sub_eq_one (MvPolynomial σ R))
  simpa [PowerSeries.rescale_mk, smul_eq_mul] using h

/-- The complete symmetric series is the inverse of the elementary product. -/
theorem completeSeries_mul_elementaryProduct :
    completeSeries σ R *
      (∏ i : σ, (1 - PowerSeries.C (X i : MvPolynomial σ R) * PowerSeries.X)) = 1 := by
  rw [completeSeries_eq_prod, ← Finset.prod_mul_distrib]
  simp_rw [geometric_mul_linear]
  exact Finset.prod_const_one

end Langlands.GeneralLinear.Spherical
