import Langlands.Geometry.Analytic.TateShearPolynomial
import Langlands.Geometry.Analytic.TateDominantPart
import Langlands.Geometry.Analytic.DistinguishedPerturbation

/-! # Making a nonzero actual Tate series distinguished by coordinate changes -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTateAlgebra

open scoped BigOperators

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

/-- The actual polynomial image of a finite coefficient part. -/
def shearPartPolynomial {n : ℕ} (b : ℕ) (f : StrictTateAlgebra (Fin (n + 1)) K)
    (S : Finset (Fin (n + 1) →₀ ℕ)) : Polynomial (StrictTateAlgebra (Fin n) K) :=
  ∑ d ∈ S, Polynomial.C (algebraMap K (StrictTateAlgebra (Fin n) K)
      (MvPowerSeries.coeff d (series _ _ f))) * shearMonomialPolynomial n b d

theorem shearPartPolynomial_natDegree_le {n b : ℕ} (hb : 0 < b)
    (f : StrictTateAlgebra (Fin (n + 1)) K) (S : Finset (Fin (n + 1) →₀ ℕ))
    (m : ℕ) (hmax : ∀ d ∈ S, baseWeight b d ≤ m) :
    (shearPartPolynomial b f S).natDegree ≤ m := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    ((shearMonomialPolynomial_natDegree n hb d).le.trans (hmax d hd))

/-- The unique highest-weight monomial supplies the exact leading
coefficient of the polynomial image. -/
theorem coeff_shearPartPolynomial_max {n b : ℕ} (hb : 0 < b)
    (f : StrictTateAlgebra (Fin (n + 1)) K) (S : Finset (Fin (n + 1) →₀ ℕ))
    (d : Fin (n + 1) →₀ ℕ) (hd : d ∈ S)
    (hmax : ∀ e ∈ S, e ≠ d → baseWeight b e < baseWeight b d) :
    (shearPartPolynomial b f S).coeff (baseWeight b d) =
      algebraMap K (StrictTateAlgebra (Fin n) K)
        (MvPowerSeries.coeff d (series _ _ f)) := by
  classical
  rw [shearPartPolynomial, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single d]
  · rw [Polynomial.coeff_C_mul, ← shearMonomialPolynomial_natDegree (K := K) n hb d,
      (shearMonomialPolynomial_monic (K := K) n hb d).coeff_natDegree, mul_one]
  · intro e he hne
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_eq_zero_of_natDegree_lt
      (by rw [shearMonomialPolynomial_natDegree n hb e]; exact hmax e he hne), mul_zero]
  · intro hnot
    exact (hnot hd).elim

variable [CompleteSpace K]

theorem norm_regroupShearHom (n b : ℕ) (f : StrictTateAlgebra (Fin (n + 1)) K) :
    ‖regroupShearHom n b f‖ = ‖f‖ := by
  change ‖regroup (powerShear (K := K) (0 : Fin (n + 1))
    (fun i => b ^ (i : ℕ)) f)‖ = ‖f‖
  rw [norm_regroup]
  have h := (powerShear_isometry (K := K) (0 : Fin (n + 1))
    (fun i => b ^ (i : ℕ))).dist_eq f 0
  simpa only [map_zero, dist_zero_right] using h

theorem regroupShearHom_coefficientPart {n : ℕ} (b : ℕ)
    (f : StrictTateAlgebra (Fin (n + 1)) K) (S : Finset (Fin (n + 1) →₀ ℕ)) :
    regroupShearHom n b (coefficientPart f S) =
      RestrictedSeries.ofPolynomial _ (shearPartPolynomial b f S) := by
  rw [coefficientPart, shearPartPolynomial, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro d _
  exact regroupShearHom_monomial n b d _

/-- Every nonzero Tate series can be made distinguished by a constructed
isometric algebra automorphism. The leading polynomial and the small
analytic remainder are both constructed from the series itself. -/
theorem exists_distinguished_coordinateChange (n : ℕ)
    (f : StrictTateAlgebra (Fin (n + 1)) K) (hf : f ≠ 0) :
    ∃ φ : StrictTateAlgebra (Fin (n + 1)) K ≃ₐ[K] StrictTateAlgebra (Fin (n + 1)) K,
      Isometry φ ∧ ∃ d : ℕ,
        RestrictedSeries.IsDistinguished (regroupEquiv n (φ f)) d := by
  classical
  let S := dominantExponents f (norm_pos_iff.mpr hf)
  have hS : S.Nonempty := dominantExponents_nonempty f hf
  let b := separatingBase S
  have hb : 0 < b :=
    lt_of_lt_of_le (by decide : 0 < 2) (separatingBase_two_le S)
  obtain ⟨d, hd, hmax⟩ := exists_unique_max_baseWeight S hS
  let m := baseWeight b d
  let p := shearPartPolynomial b f S
  let φ := powerShear (K := K) (0 : Fin (n + 1)) (fun i => b ^ (i : ℕ))
  let h := regroupShearHom n b (f - coefficientPart f S)
  have hdegree : p.natDegree ≤ m := by
    apply shearPartPolynomial_natDegree_le hb f S m
    intro e he
    by_cases hed : e = d
    · subst e
      exact le_rfl
    · exact (hmax e he hed).le
  have hleading : p.coeff m =
      algebraMap K (StrictTateAlgebra (Fin n) K)
        (MvPowerSeries.coeff d (series _ _ f)) :=
    coeff_shearPartPolynomial_max hb f S d hd hmax
  have ha_norm : ‖MvPowerSeries.coeff d (series _ _ f)‖ = ‖f‖ := by
    apply le_antisymm (norm_coeff_le _ _ f d)
    exact (mem_dominantExponents f _ d).mp hd
  have ha_ne : MvPowerSeries.coeff d (series _ _ f) ≠ 0 := by
    apply norm_pos_iff.mp
    rw [ha_norm]
    exact norm_pos_iff.mpr hf
  have hp_norm : ‖RestrictedSeries.ofPolynomial _ p‖ ≤ ‖f‖ := by
    rw [← regroupShearHom_coefficientPart, norm_regroupShearHom]
    exact norm_coefficientPart_le f S
  have hp_leadnorm : ‖RestrictedSeries.coeff _ m (RestrictedSeries.ofPolynomial _ p)‖ =
      ‖f‖ := by
    rw [RestrictedSeries.coeff_ofPolynomial, hleading, norm_algebraMap, ha_norm]
  have hp_dist : RestrictedSeries.IsDistinguished (RestrictedSeries.ofPolynomial _ p) m := by
    refine ⟨?_, ?_, ?_⟩
    · rw [RestrictedSeries.coeff_ofPolynomial, hleading]
      exact (isUnit_iff_ne_zero.mpr ha_ne).map (algebraMap K (StrictTateAlgebra (Fin n) K))
    · intro k
      rw [hp_leadnorm]
      exact ((RestrictedSeries.norm_le_iff _ _ (norm_nonneg _)).mp le_rfl k).trans hp_norm
    · intro k hk
      rw [hp_leadnorm, RestrictedSeries.coeff_ofPolynomial,
        Polynomial.coeff_eq_zero_of_natDegree_lt (hdegree.trans_lt hk), norm_zero]
      exact norm_pos_iff.mpr hf
  have hh : ‖h‖ < ‖RestrictedSeries.coeff _ m (RestrictedSeries.ofPolynomial _ p)‖ := by
    rw [hp_leadnorm]
    change ‖regroupShearHom n b (f - coefficientPart f S)‖ < ‖f‖
    rw [norm_regroupShearHom]
    exact norm_sub_dominantPart_lt f (norm_pos_iff.mpr hf)
  have heq : regroupEquiv n (φ f) = RestrictedSeries.ofPolynomial _ p + h := by
    change regroupShearHom n b f =
      RestrictedSeries.ofPolynomial _ (shearPartPolynomial b f S) +
        regroupShearHom n b (f - coefficientPart f S)
    rw [← regroupShearHom_coefficientPart, map_sub]
    abel
  refine ⟨φ, powerShear_isometry _ _, m, ?_⟩
  rw [heq]
  exact hp_dist.add_of_norm_lt h hh

end Langlands.Analytic.StrictTateAlgebra
