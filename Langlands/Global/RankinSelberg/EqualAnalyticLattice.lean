import Langlands.Global.RankinSelberg.EqualAnalyticDominated
import Langlands.Global.Hecke.LatticePoissonGeneral

/-! # Lattice sums over rational row vectors with bounded denominators

For a nonzero `D ∈ 𝒪`, the rational row vectors `ξ ∈ F^n` with `D ξ ∈ 𝒪^n` form a lattice in
`(F_∞)^n`, and `Σ_ξ (1 + ‖ξ‖_∞)^(-r)` converges for `r > n [F : ℚ]`. Also, an element of `F`
which is integral at every finite place lies in `𝒪`.
-/

noncomputable section
universe u
open NumberField Module
open scoped Classical
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.EqualAnalytic

open Langlands.Global Langlands.Automorphic.CuspidalWhittaker

variable (F : Type u) [Field F] [NumberField F]

/-- An element of `F` integral at every finite place lies in `𝒪`. -/
theorem exists_eq_algebraMap_of_integral (x : F)
    (hx : algebraMap F (FiniteAdeles F) x ∈ integralFiniteAdeles F) :
    ∃ a : 𝓞 F, algebraMap (𝓞 F) F a = x := by
  have : x ∈ (algebraMap (RingOfIntegers F) F).range := by
    refine IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one F x fun v => ?_
    have h := (mem_integralFiniteAdeles F _).mp hx v
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at h
    change Valued.v ((x : v.adicCompletion F)) ≤ 1 at h
    rwa [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
  exact this

/-- Rational row vectors `ξ` with `D ξ ∈ 𝒪^n`. -/
def IntegralRows (n : ℕ) (D : 𝓞 F) : Set (Fin n → F) :=
  {ξ | ∀ j, ∃ a : 𝓞 F, algebraMap (𝓞 F) F D * ξ j = algebraMap (𝓞 F) F a}

/-- The archimedean image `(ξ_j)_j ∈ (F_∞)^n` of a rational row vector. -/
def rowEmbedding (n : ℕ) (ξ : Fin n → F) : ArchRow F n := fun j => mixedEmbedding F (ξ j)

theorem mixedEmbedding_integer_eq_sum (a : 𝓞 F) :
    mixedEmbedding F (algebraMap (𝓞 F) F a) =
      ∑ k, ((RingOfIntegers.basis F).repr a k : ℝ) • mixedEmbedding.latticeBasis F k := by
  conv_lhs => rw [← (RingOfIntegers.basis F).sum_repr a]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, map_zsmul, mixedEmbedding.latticeBasis_apply, integralBasis_apply,
    ← Int.cast_smul_eq_zsmul ℝ]

/-- The basis `Pi.single j (latticeBasis k)` of `(F_∞)^n`. -/
def rowBasis (n : ℕ) :
    Module.Basis ((_ : Fin n) × Free.ChooseBasisIndex ℤ (𝓞 F)) ℝ (ArchRow F n) :=
  Pi.basis fun _ => mixedEmbedding.latticeBasis F

theorem rowBasis_latticeVec (n : ℕ) (m : ((_ : Fin n) × Free.ChooseBasisIndex ℤ (𝓞 F)) → ℤ)
    (j : Fin n) :
    Hecke.latticeVec (rowBasis F n) m j =
      ∑ k, (m ⟨j, k⟩ : ℝ) • mixedEmbedding.latticeBasis F k := by
  rw [Hecke.latticeVec_eq_sum, Finset.sum_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single j]
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp [rowBasis, Pi.basis_apply]
  · intro l _ hl
    refine Finset.sum_eq_zero fun k _ => ?_
    simp [rowBasis, Pi.basis_apply, Ne.symm hl]
  · simp

/-- **Lattice sums.** `Σ_{ξ ∈ F^n, D ξ ∈ 𝒪^n} (1 + ‖ξ‖_∞)^(-r)` converges for `r > n [F : ℚ]`. -/
theorem summable_integralRows (n : ℕ) (D : 𝓞 F) (hD : D ≠ 0) {r : ℝ}
    (hr : ((n * finrank ℚ F : ℕ) : ℝ) < r) :
    Summable fun ξ : IntegralRows F n D => (1 + ‖rowEmbedding F n ξ.1‖) ^ (-r) := by
  have hdim : (finrank ℝ (ArchRow F n) : ℝ) < r := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mixedEmbedding.finrank]
    exact hr
  have hsum := Hecke.summable_one_add_norm_latticeVec_rpow (rowBasis F n) hdim
  choose a ha using fun ξ : IntegralRows F n D => ξ.2
  let m : IntegralRows F n D → ((_ : Fin n) × Free.ChooseBasisIndex ℤ (𝓞 F)) → ℤ :=
    fun ξ p => (RingOfIntegers.basis F).repr (a ξ p.1) p.2
  have hDne : algebraMap (𝓞 F) F D ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hD
  have hinj : Function.Injective m := by
    intro ξ ξ' h
    apply Subtype.ext
    funext j
    have hj : a ξ j = a ξ' j := by
      apply (RingOfIntegers.basis F).repr.injective
      ext k
      exact congrFun h ⟨j, k⟩
    have := (ha ξ j).trans ((congrArg _ hj).trans (ha ξ' j).symm)
    exact mul_left_cancel₀ hDne this
  have hvec : ∀ ξ, Hecke.latticeVec (rowBasis F n) (m ξ) =
      fun j => mixedEmbedding F (algebraMap (𝓞 F) F D) * rowEmbedding F n ξ.1 j := by
    intro ξ
    funext j
    rw [rowBasis_latticeVec, rowEmbedding, ← map_mul, ha ξ j, mixedEmbedding_integer_eq_sum]
  set c := ‖mixedEmbedding F (algebraMap (𝓞 F) F D)‖
  have hr0 : 0 ≤ r := le_trans (Nat.cast_nonneg _) hr.le
  refine (hsum.comp_injective hinj).mul_left ((1 + c) ^ r) |>.of_nonneg_of_le
    (fun ξ => by positivity) fun ξ => ?_
  simp only [Function.comp_apply]
  apply Hecke.rpow_neg_le_of_le_mul (by positivity) (by positivity) hr0
  rw [hvec]
  have hnorm : ‖fun j => mixedEmbedding F (algebraMap (𝓞 F) F D) * rowEmbedding F n ξ.1 j‖ ≤
      c * ‖rowEmbedding F n ξ.1‖ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_
    exact (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left (norm_le_pi_norm (rowEmbedding F n ξ.1) j) (norm_nonneg _))
  have hc0 : 0 ≤ c := norm_nonneg _
  have hn0 : 0 ≤ ‖rowEmbedding F n ξ.1‖ := norm_nonneg _
  nlinarith

end Langlands.Global.RankinSelbergGlobal.EqualAnalytic
