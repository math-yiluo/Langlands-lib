import Langlands.Representation.Archimedean.ComplexGLTwoNoncompactOperators
import Langlands.Representation.Archimedean.ComplexJacquetTorus
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Highest weight vectors in `(𝔤𝔩_2(ℂ), U(2))`-submodules of the principal series

Let `S` be a nonzero `(𝔤, K)`-submodule of the `U(2)`-finite principal series `X(d)`. Then `S`
contains a vector `v` whose noncompact picture is exactly
`φ_b(z) = (1 + |z|²)^(-(q + 1 + b)) z̄^b` for some `b ∈ ℕ` (`exists_phiB_mem`).

* A finite-dimensional space stable under `H` and `X₊` with `[H, X₊] = i X₊` contains a
  common eigenvector of `H` killed by `X₊` (`exists_eigen_kernel`): take an eigenvalue of `H`
  with largest imaginary part.
* The `U(2)`-span of a nonzero vector of `S` is finite-dimensional and lies in `S`, which gives
  such a vector in `S` (`exists_eH_eXp`).
* Its `H`-eigenvalue is `i k` with `k ∈ ℤ`, because `exp(2π i E_00) = 1`
  (`exists_int_of_eH`).
* In the noncompact picture `H v = i (l_1 + b) v` and `X₊ v = 0` read
  `z ∂φ - z̄ ∂̄φ = -b φ` and `∂φ + z̄² ∂̄φ + (q + 1) z̄ φ = 0`. Hence
  `φ (1 + |z|²)^(q + 1 + b) z̄^(-b)` has vanishing derivative on the connected set `ℂ ∖ {0}`,
  so it is a constant `c` there (`ncp_highest`). Continuity of `φ` at `0` forces `b ≥ 0`, and
  `c ≠ 0` because the noncompact picture is injective (`highest_eq_phiB`).
-/

noncomputable section

open scoped TensorProduct Matrix

open Complex ComplexConjugate

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean Langlands.GeneralLinear

open scoped Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false

namespace ComplexGLTwoNoncompact

/-! ## Linear algebra -/

/-- If `H` and `X` preserve a nonzero finite-dimensional subspace `W` and `[H, X] = i X`, then
`W` contains an eigenvector of `H` killed by `X`. -/
theorem exists_eigen_kernel {V : Type*} [AddCommGroup V] [Module ℂ V] (W : Submodule ℂ V)
    [FiniteDimensional ℂ W] (hW : W ≠ ⊥) (H X : Module.End ℂ V)
    (hH : ∀ w ∈ W, H w ∈ W) (hX : ∀ w ∈ W, X w ∈ W)
    (hc : ∀ v, H (X v) = X (H v) + I • X v) :
    ∃ v ∈ W, v ≠ 0 ∧ ∃ μ : ℂ, H v = μ • v ∧ X v = 0 := by
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  set HW : Module.End ℂ W := H.restrict hH with hHW
  obtain ⟨μ, hμ, hmax⟩ := Set.exists_max_image {μ : ℂ | HW.HasEigenvalue μ} (fun μ => μ.im)
    HW.finite_hasEigenvalue (Module.End.exists_eigenvalue HW)
  obtain ⟨w, hw⟩ := (show HW.HasEigenvalue μ from hμ).exists_hasEigenvector
  have hHw : H w = μ • (w : V) := congrArg Subtype.val hw.apply_eq_smul
  refine ⟨w, w.2, fun h => hw.2 (Subtype.ext h), μ, hHw, ?_⟩
  by_contra hXw
  have hev : HW.HasEigenvalue (μ + I) := by
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨X w, hX w w.2⟩)
      (Module.End.hasEigenvector_iff.mpr ⟨?_, ?_⟩)
    · rw [Module.End.mem_eigenspace_iff]
      apply Subtype.ext
      change H (X w) = (μ + I) • X w
      rw [hc, hHw, map_smul, add_smul]
    · intro h
      exact hXw (congrArg Subtype.val h)
  have h := hmax _ hev
  simp only [Complex.add_im, Complex.I_im] at h
  linarith

/-! ## A highest weight vector in a submodule -/

variable {d : Fin 2 → ComplexCharacterData}

/-- A nonzero `(𝔤, K)`-submodule of `X(d)` contains an eigenvector of `H` killed by `X₊`. -/
theorem exists_eH_eXp (S : Submodule ℂ (Xd d))
    (hS : IsGKSubmodule (complexStandardRep 2 (List.ofFn d)) (πd d) S) (hne : S ≠ ⊥) :
    ∃ v ∈ S, v ≠ 0 ∧ ∃ μ : ℂ, πd d eH v = μ • v ∧ πd d eXp v = 0 := by
  obtain ⟨v0, hv0, hv0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hgk := isComplexGKModule_complexStandardModule 2 (List.ofFn d)
  have hWfin : FiniteDimensional ℂ
      (FiniteVectors.orbitSpan (complexStandardRep 2 (List.ofFn d)) v0) := hgk.1 v0
  have hWS : FiniteVectors.orbitSpan (complexStandardRep 2 (List.ofFn d)) v0 ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact hS.1 k v0 hv0
  have hWne : FiniteVectors.orbitSpan (complexStandardRep 2 (List.ofFn d)) v0 ≠ ⊥ := by
    intro h
    have hmem := FiniteVectors.self_mem_orbitSpan (complexStandardRep 2 (List.ofFn d)) v0
    rw [h, Submodule.mem_bot] at hmem
    exact hv0ne hmem
  have hWst : ∀ k, ∀ w ∈ FiniteVectors.orbitSpan (complexStandardRep 2 (List.ofFn d)) v0,
      complexStandardRep 2 (List.ofFn d) k w ∈
        FiniteVectors.orbitSpan (complexStandardRep 2 (List.ofFn d)) v0 :=
    fun k w hw => (FiniteVectors.orbitSubrepresentation _ v0).apply_mem_toSubmodule k hw
  obtain ⟨hH, hX⟩ := compact_stable _ hWst
  obtain ⟨v, hvW, hv0, μ, hμ, hXv⟩ :=
    exists_eigen_kernel _ hWne (πd d eH) (πd d eXp) hH hX eH_eXp
  exact ⟨v, hWS hvW, hv0, μ, hμ, hXv⟩

/-! ## Integrality of the weight -/

theorem skewExp_two_pi_Y0 :
    skewExp ((2 * Real.pi) • Y0) (star_real_smul_of_skew star_Y0 (2 * Real.pi)) = 1 := by
  apply Subtype.ext
  rw [coe_skewExp]
  have h : (2 * Real.pi) • Y0 = diagI ![2 * Real.pi, 0] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Y0, diagI, Matrix.diagonal]
  rw [h, exp_diagI]
  change _ = (1 : Matrix (Fin 2) (Fin 2) ℂ)
  rw [← Matrix.diagonal_one]
  congr 1
  funext j
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    push_cast
    exact Complex.exp_two_pi_mul_I
  · simp

/-- The `H`-eigenvalue of a nonzero vector is `i k` with `k ∈ ℤ`. -/
theorem exists_int_of_eH {v : Xd d} (hv : v ≠ 0) {μ : ℂ} (hμ : πd d eH v = μ • v) :
    ∃ k : ℤ, μ = I * k := by
  have hgk := isComplexGKModule_complexStandardModule 2 (List.ofFn d)
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_ne_zero ℂ hv
  have hμ' : complexStandardLie 2 (List.ofFn d) ((1 : ℂ) ⊗ₜ[ℝ] Y0) v = μ • v := hμ
  set φ : ℝ → ℂ := fun t => ℓ (complexStandardRep 2 (List.ofFn d)
      (skewExp (t • Y0) (star_real_smul_of_skew star_Y0 t)) v) with hφ
  have hderiv : ∀ s, HasDerivAt φ (μ * φ s) s := by
    intro s
    have h := hasDerivAt_skewExp hgk star_Y0 ℓ v s
    rw [hμ', map_smul, map_smul, smul_eq_mul] at h
    exact h
  have h1 := Langlands.Automorphic.OperatorRealization.eq_exp_mul_of_hasDerivAt hderiv
    (2 * Real.pi)
  have h0 : φ 0 = ℓ v := by
    simp only [hφ, skewExp_zero_smul star_Y0, map_one, Module.End.one_apply]
  have h2 : φ (2 * Real.pi) = ℓ v := by
    simp only [hφ, skewExp_two_pi_Y0, map_one, Module.End.one_apply]
  rw [h0, h2] at h1
  have hexp : Complex.exp (μ * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
    have h3 : Complex.exp (μ * ((2 * Real.pi : ℝ) : ℂ)) * ℓ v = 1 * ℓ v := by
      rw [one_mul]
      exact h1.symm
    exact mul_right_cancel₀ hℓ h3
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp hexp
  refine ⟨m, ?_⟩
  have hpi : (2 * Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  apply mul_left_cancel₀ hpi
  push_cast at hm
  linear_combination hm

/-! ## The differential equations -/

theorem differentiable_ncpL (v : Xd d) : Differentiable ℝ (ncpL d v) :=
  (ComplexSwapJacquet.contDiff_apply_chart (ComplexSwapJacquet.mem_of_mem_kFs v.2).1 0 1
    hj01).differentiable (by simp)

theorem continuous_pw (σ : ℂ) : Continuous (pw σ) :=
  continuous_iff_continuousAt.mpr fun z => (hasWirt_pw σ z).differentiableAt.continuousAt

variable (d) in
/-- `φ_b(z) = (1 + |z|²)^(-(q + 1 + b)) z̄^b`. -/
def phiB (b : ℕ) (z : ℂ) : ℂ := pw (-(qq d + 1 + b)) z * conj z ^ b

variable (d) in
theorem continuous_phiB (b : ℕ) : Continuous (phiB d b) :=
  (continuous_pw _).mul (Complex.continuous_conj.pow b)

/-- If `H v = i (l_1 + b) v` and `X₊ v = 0`, then `φ_v (1 + |z|²)^(q + 1 + b) z̄^(-b)` is
constant on `ℂ ∖ {0}`. -/
theorem ncp_highest {v : Xd d} {b : ℤ}
    (hH : πd d eH v = (I * (((d 1).weight + b : ℤ) : ℂ)) • v) (hX : πd d eXp v = 0) :
    ∃ c : ℂ, ∀ z : ℂ, z ≠ 0 →
      ncpL d v z * pw (qq d + 1 + b) z * conj z ^ (-b) = c := by
  have hdiff := differentiable_ncpL v
  have key : ∀ z : ℂ, z ≠ 0 →
      HasWirt (fun x => ncpL d v x * pw (qq d + 1 + b) x * conj x ^ (-b)) 0 0 z := by
    intro z hz
    have hu : conj z ≠ 0 := (map_ne_zero _).mpr hz
    have h1 := ncpL_eH v z
    rw [hH, map_smul, Pi.smul_apply, smul_eq_mul] at h1
    push_cast at h1
    have h2 := ncpL_eXp v z
    rw [hX, map_zero, Pi.zero_apply] at h2
    have hE1 : conj z * dzb (ncpL d v) z - b * ncpL d v z - z * dz (ncpL d v) z = 0 := by
      apply mul_left_cancel₀ I_ne_zero
      linear_combination -h1
    have hkey : W z * dz (ncpL d v) z + (qq d + 1 + b) * conj z * ncpL d v z = 0 := by
      unfold W
      linear_combination -h2 - conj z * hE1
    have hpw : pw (qq d + 1 + b) z = pw (qq d + 1 + b - 1) z * W z := by
      rw [pw_sub_one, div_mul_cancel₀ _ (W_ne_zero z)]
    have hzp : conj z ^ (-b) = conj z ^ (-b - 1) * conj z := by
      rw [← zpow_add_one₀ hu, sub_add_cancel]
    have h := ((hasWirt_of_differentiableAt (hdiff z)).mul (hasWirt_pw (qq d + 1 + b) z)).mul
      ((hasWirt_conj z).zpow hu (-b))
    refine h.congr ?_ ?_
    · rw [hpw]
      linear_combination (conj z ^ (-b) * pw (qq d + 1 + b - 1) z) * hkey
    · rw [hpw, hzp]
      push_cast
      linear_combination (conj z ^ (-b - 1) * pw (qq d + 1 + b - 1) z) *
        (W z * hE1 + z * hkey)
  have hconn : IsPreconnected ({0}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num) 0).isPreconnected
  obtain ⟨c, hc⟩ := isOpen_compl_singleton.exists_is_const_of_fderiv_eq_zero hconn
    (fun z hz => (key z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => by rw [(key z hz).fderiv, wirt_zero]; rfl)
  exact ⟨c, fun z hz => hc z hz⟩

/-- A nonzero highest weight vector has `b ≥ 0` and noncompact picture `c φ_b` with
`c ≠ 0`. -/
theorem highest_eq_phiB {v : Xd d} (hv : v ≠ 0) {b : ℤ}
    (hH : πd d eH v = (I * (((d 1).weight + b : ℤ) : ℂ)) • v) (hX : πd d eXp v = 0) :
    ∃ n : ℕ, (n : ℤ) = b ∧ ∃ c : ℂ, c ≠ 0 ∧ ncpL d v = c • phiB d n := by
  obtain ⟨c, hc⟩ := ncp_highest hH hX
  have hcont := (differentiable_ncpL v).continuous
  have hdense : Dense ({0}ᶜ : Set ℂ) := dense_compl_singleton 0
  have hzero : (∀ z : ℂ, z ≠ 0 → ncpL d v z = 0) → False := by
    intro h
    apply hv
    apply ncpL_injective
    rw [map_zero]
    exact Continuous.ext_on hdense hcont continuous_const h
  rcases le_or_gt 0 b with hb | hb
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hb
    have heq : ∀ z : ℂ, z ≠ 0 → ncpL d v z = c * phiB d n z := by
      intro z hz
      have h := hc z hz
      simp only [Int.cast_natCast] at h
      have hu : conj z ≠ 0 := (map_ne_zero _).mpr hz
      have hp : pw (-(qq d + 1 + n)) z * pw (qq d + 1 + n) z = 1 := by
        rw [← pw_add, neg_add_cancel, pw_zero]
      rw [phiB, ← h, zpow_neg, zpow_natCast]
      rw [show ncpL d v z * pw (qq d + 1 + n) z * (conj z ^ n)⁻¹ *
          (pw (-(qq d + 1 + n)) z * conj z ^ n) =
          ncpL d v z * (pw (-(qq d + 1 + n)) z * pw (qq d + 1 + n) z) *
            ((conj z ^ n)⁻¹ * conj z ^ n) by ring,
        hp, inv_mul_cancel₀ (pow_ne_zero n hu), mul_one, mul_one]
    refine ⟨n, rfl, c, ?_, ?_⟩
    · rintro rfl
      exact hzero fun z hz => by rw [heq z hz, zero_mul]
    · exact Continuous.ext_on hdense hcont (continuous_const.mul (continuous_phiB d n)) heq
  · exfalso
    obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat hb.le
    subst hn
    have hn0 : n ≠ 0 := by
      rintro rfl
      simp at hb
    have heq : ∀ z : ℂ, z ≠ 0 →
        ncpL d v z * pw (qq d + 1 + ((-(n : ℤ) : ℤ) : ℂ)) z * conj z ^ n = c := by
      intro z hz
      have h := hc z hz
      rwa [neg_neg, zpow_natCast] at h
    have hF := Continuous.ext_on hdense
      ((hcont.mul (continuous_pw _)).mul (Complex.continuous_conj.pow n)) continuous_const heq
    have h0 : ncpL d v 0 * pw (qq d + 1 + ((-(n : ℤ) : ℤ) : ℂ)) 0 * conj (0 : ℂ) ^ n = c :=
      congrFun hF 0
    rw [map_zero, zero_pow hn0, mul_zero] at h0
    apply hzero
    intro z hz
    have h := heq z hz
    rw [← h0] at h
    have hu : conj z ≠ 0 := (map_ne_zero _).mpr hz
    rcases mul_eq_zero.mp h with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact h''
      · exact absurd h'' (pw_ne_zero _ _)
    · exact absurd h' (pow_ne_zero n hu)

/-- A nonzero `(𝔤, K)`-submodule of `X(d)` contains a vector with noncompact picture `φ_b`
for some `b ∈ ℕ`. -/
theorem exists_phiB_mem (S : Submodule ℂ (Xd d))
    (hS : IsGKSubmodule (complexStandardRep 2 (List.ofFn d)) (πd d) S) (hne : S ≠ ⊥) :
    ∃ (n : ℕ) (v : Xd d), v ∈ S ∧ ncpL d v = phiB d n := by
  obtain ⟨v, hvS, hv0, μ, hμ, hX⟩ := exists_eH_eXp S hS hne
  obtain ⟨k, hk⟩ := exists_int_of_eH hv0 hμ
  have hH : πd d eH v = (I * (((d 1).weight + (k - (d 1).weight) : ℤ) : ℂ)) • v := by
    rw [hμ, hk, show (d 1).weight + (k - (d 1).weight) = k by ring]
  obtain ⟨n, -, c, hc, hn⟩ := highest_eq_phiB hv0 hH hX
  refine ⟨n, c⁻¹ • v, S.smul_mem _ hvS, ?_⟩
  rw [map_smul, hn, smul_smul, inv_mul_cancel₀ hc, one_smul]

end ComplexGLTwoNoncompact

end Langlands.Archimedean
