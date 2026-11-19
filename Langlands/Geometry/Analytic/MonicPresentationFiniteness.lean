import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeSeriesMap
import Langlands.Geometry.Analytic.PolynomialDivision
import Langlands.Geometry.Analytic.FullRecognitionFiniteMorphisms

/-! # Finiteness from bounded monic equations on presentation coordinates -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open Filter Polynomial GeneralizedTateAlgebra
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : PresentedAffinoidAlgebra K}

/-- Suppose that each presentation radius is the norm of `c i` and that
each coordinate divided by `c i` satisfies a monic polynomial with
unit-ball coefficients over `A`. Then the actual bounded map is finite. -/
theorem finite_of_monic_normalized_coordinates
    (f : BoundedAlgHom K A B)
    (c : Fin B.arity → K) (hc : ∀ i, ‖c i‖ = B.polyradius i)
    (p : Fin B.arity → Polynomial A) (hm : ∀ i, (p i).Monic)
    (hu : ∀ i n, ‖(p i).coeff n‖ ≤ 1)
    (hz : ∀ i, (p i).eval₂ f.toAlgHom.toRingHom ((c i)⁻¹ • coordinate K B i) = 0) :
    f.toAlgHom.toRingHom.Finite := by
  classical
  let x : Fin B.arity → B := fun i => (c i)⁻¹ • coordinate K B i
  let r (i : Fin B.arity) (n : ℕ) : Polynomial A := Polynomial.X ^ n %ₘ p i
  have hr (i : Fin B.arity) (n k : ℕ) : ‖(r i n).coeff k‖ ≤ 1 := by
    apply (((r i n).le_supNorm k).trans
      (polynomial_division_supNorm_le (Polynomial.X ^ n) (p i) (hm i) (hu i)).2).trans
    apply (polynomial_supNorm_le_iff _ _).mpr
    intro l
    rw [coeff_X_pow]
    split_ifs
    · exact norm_one_le K A
    · simp
  have hpow (i : Fin B.arity) (n : ℕ) :
      x i ^ n = ∑ k : Fin (p i).natDegree, f ((r i n).coeff k) * x i ^ (k : ℕ) := by
    have h := congrArg (fun q : Polynomial A => q.eval₂ f.toAlgHom.toRingHom (x i))
      (modByMonic_add_div (Polynomial.X ^ n) (p i))
    change (r i n + p i * ((Polynomial.X ^ n) /ₘ p i)).eval₂ _ _ =
      (Polynomial.X ^ n).eval₂ _ _ at h
    rw [eval₂_add, eval₂_mul, hz i, zero_mul, add_zero, eval₂_pow, eval₂_X] at h
    rw [← h]
    have hsum : (∑ k : Fin (p i).natDegree, Polynomial.monomial k ((r i n).coeff k)) =
        r i n := sum_modByMonic_coeff (hm i) degree_le_natDegree
    conv_lhs => rw [← hsum]
    simp only [eval₂_finsetSum, eval₂_monomial]
    rfl
  let J := ∀ i : Fin B.arity, Fin (p i).natDegree
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let b (j : J) : B := ∏ i, x i ^ (j i : ℕ)
  let a (d : Fin B.arity →₀ ℕ) (j : J) : A := ∏ i, (r i (d i)).coeff (j i)
  have ha (d : Fin B.arity →₀ ℕ) (j : J) : ‖a d j‖ ≤ 1 := by
    suffices ∀ t : Finset (Fin B.arity), ‖∏ i ∈ t, (r i (d i)).coeff (j i)‖ ≤ 1
      from this Finset.univ
    intro t
    induction t using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using norm_one_le K A
    | insert i t hi ht =>
      rw [Finset.prod_insert hi]
      exact (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_right
        (hr i (d i) (j i)) (norm_nonneg _)).trans (by simpa only [one_mul] using ht))
  have hbox (d : Fin B.arity →₀ ℕ) : ∏ i, x i ^ d i = ∑ j : J, f (a d j) * b j := by
    calc
      _ = ∏ i, ∑ k : Fin (p i).natDegree, f ((r i (d i)).coeff k) * x i ^ (k : ℕ) :=
        Finset.prod_congr rfl (fun i _ => hpow i (d i))
      _ = ∑ j : J, ∏ i, f ((r i (d i)).coeff (j i)) * x i ^ (j i : ℕ) :=
        Fintype.prod_sum _
      _ = _ := by
        simp only [a, b, Finset.prod_mul_distrib, map_prod]
  let s (d : Fin B.arity →₀ ℕ) : K := ∏ i, c i ^ d i
  have hs (d : Fin B.arity →₀ ℕ) : ‖s d‖ = B.polyradius.weight d := by
    simp only [s, PositivePolyradius.weight, norm_prod, norm_pow, hc]
    exact (Finsupp.prod_fintype d (fun i n => B.polyradius i ^ n) (fun _ => pow_zero _)).symm
  have hcoord (i : Fin B.arity) : coordinate K B i = algebraMap K B (c i) * x i := by
    have hci : c i ≠ 0 := norm_pos_iff.mp ((hc i).symm ▸ B.polyradius.positive i)
    rw [← Algebra.smul_def]
    change _ = c i • ((c i)⁻¹ • coordinate K B i)
    rw [smul_smul, mul_inv_cancel₀ hci, one_smul]
  have hmon (d : Fin B.arity →₀ ℕ) :
      StrictTateAlgebra.monomialValue (Fin B.arity) B (coordinate K B) d =
        algebraMap K B (s d) * (∏ i, x i ^ d i) := by
    unfold StrictTateAlgebra.monomialValue
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp only [hcoord, mul_pow, Finset.prod_mul_distrib, s, map_prod, map_pow]
  let L := f.coefficientMap (b ∘ e.symm)
  refine f.finite_iff_exists_surjective_coefficientMap.mpr ⟨_, b ∘ e.symm, fun z => ?_⟩
  change ∃ v, L v = z
  obtain ⟨g, rfl⟩ := presentationMap_surjective K B z
  let coeff (d : Fin B.arity →₀ ℕ) : K := MvPowerSeries.coeff d (series B.polyradius K g)
  let v (d : Fin B.arity →₀ ℕ) (k : Fin (Fintype.card J)) : A :=
    (coeff d * s d) • a d (e.symm k)
  have hv : Summable v := by
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero (fun _ => norm_nonneg _) (fun d => ?_) g.property
    apply (pi_norm_le_iff_of_nonneg
      (mul_nonneg (norm_nonneg (coeff d)) (B.polyradius.weight_pos d).le)).mpr
    intro k
    change ‖(coeff d * s d) • a d (e.symm k)‖ ≤ ‖coeff d‖ * B.polyradius.weight d
    calc
      _ ≤ ‖coeff d * s d‖ * ‖a d (e.symm k)‖ := norm_smul_le _ _
      _ ≤ ‖coeff d * s d‖ * 1 := mul_le_mul_of_nonneg_left (ha d (e.symm k)) (norm_nonneg _)
      _ = _ := by rw [mul_one, norm_mul, hs]
  have hvL (d : Fin B.arity →₀ ℕ) : L (v d) =
      presentationMap K B (monomial B.polyradius K d (coeff d)) := by
    rw [GeneralizedTateAlgebra.map_monomial]
    change L (v d) = algebraMap K B (coeff d) *
      StrictTateAlgebra.monomialValue (Fin B.arity) B (coordinate K B) d
    rw [hmon, hbox, ← mul_assoc, ← map_mul, Finset.mul_sum]
    change (∑ k, f (v d k) * b (e.symm k)) = _
    rw [← Equiv.sum_comp e]
    simp only [v, Equiv.symm_apply_apply, Algebra.smul_def, map_mul, AlgHom.commutes, mul_assoc]
  refine ⟨∑' d, v d, ?_⟩
  rw [L.map_tsum hv]
  simp_rw [hvL]
  exact ((hasSum_monomials B.polyradius K g).mapL
    (presentationMap K B).toContinuousLinearMap).tsum_eq

end Langlands.Analytic.PresentedAffinoidAlgebra
