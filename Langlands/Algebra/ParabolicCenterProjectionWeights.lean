import Langlands.Algebra.LieWeightCenterProjection
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Analysis.Complex.Basic

/-! # Weight bases for an abelian subspace and a regular grading element -/

noncomputable section

universe v

set_option autoImplicit false

namespace Langlands.Algebra.ParabolicCenterProjection

open Langlands.Algebra.LieWeightProjection

variable {g : Type v} [LieRing g] [LieAlgebra ℂ g]
  {𝔥 : Submodule ℂ g} {I : Type v} {b : Module.Basis I ℂ g} {wt : I → 𝔥 →ₗ[ℂ] ℂ}

section WeightVectors

variable (heig : ∀ i (h : 𝔥), ⁅(h : g), b i⁆ = wt i h • b i)

include heig in
/-- A common eigenvector of `ad 𝔥` with eigenvalues `μ` has coordinates only on basis vectors of
weight `μ`. -/
theorem wt_eq_of_repr_ne_zero {x : g} {μ : 𝔥 → ℂ} (hx : ∀ h : 𝔥, ⁅(h : g), x⁆ = μ h • x)
    {c : I} (hc : b.repr x c ≠ 0) : ∀ h : 𝔥, wt c h = μ h := by
  intro h
  have h1 := mem_eigenSpan_of_ad b (fun i => wt i h) (h : g) (fun i => heig i h) (μ h) (hx h)
  rw [Module.Basis.mem_span_image] at h1
  exact h1 (Finsupp.mem_support_iff.mpr hc)

include heig in
theorem lie_basis_eig (e i : I) (h : 𝔥) :
    ⁅(h : g), ⁅b e, b i⁆⁆ = (wt e h + wt i h) • ⁅b e, b i⁆ := by
  rw [leibniz_lie, heig, heig, smul_lie, lie_smul, add_smul]

variable (B : LinearMap.BilinForm ℂ g) (hBinv : ∀ x y z, B ⁅x, y⁆ z = B x ⁅y, z⁆)

include hBinv in
theorem form_lie_add_form_lie (h x y : g) : B ⁅h, x⁆ y + B x ⁅h, y⁆ = 0 := by
  rw [← hBinv x h y, ← lie_skew x h, map_neg, LinearMap.neg_apply, add_neg_cancel]

include heig hBinv in
/-- The form pairs only basis vectors of opposite weights. -/
theorem wt_eq_neg_of_form_ne_zero {e i : I} (h0 : B (b e) (b i) ≠ 0) : wt e = -wt i := by
  ext h
  have := form_lie_add_form_lie B hBinv (h : g) (b e) (b i)
  rw [heig, heig, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul,
    ← add_mul] at this
  rcases mul_eq_zero.mp this with h1 | h1
  · rw [LinearMap.neg_apply]; exact eq_neg_of_add_eq_zero_left h1
  · exact absurd h1 h0

end WeightVectors

section Regular

variable [Fintype I]

/-- There is an element of `𝔥` on which the real part of every nonzero weight is nonzero. -/
theorem exists_re_ne_zero : ∃ h' : 𝔥, ∀ i, wt i ≠ 0 → (wt i h').re ≠ 0 := by
  classical
  let J := {i : I // wt i ≠ 0}
  let p : J → Submodule ℝ 𝔥 := fun i =>
    LinearMap.ker (Complex.reLm.comp ((wt i.1).restrictScalars ℝ))
  have hp : ∀ i, p i ≠ ⊤ := by
    intro i htop
    obtain ⟨h₀, hh₀⟩ : ∃ h₀ : 𝔥, wt i.1 h₀ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact i.2 (LinearMap.ext hcon)
    have hmem : ((wt i.1 h₀)⁻¹ • h₀ : 𝔥) ∈ p i := htop ▸ Submodule.mem_top
    simp only [p, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_restrictScalars, map_smul, smul_eq_mul, inv_mul_cancel₀ hh₀,
      Complex.reLm_coe, Complex.one_re] at hmem
    exact one_ne_zero hmem
  have hcard : (Finset.univ : Finset J).card < ENat.card ℝ := by
    rw [ENat.card_eq_top_of_infinite]
    exact ENat.natCast_lt_top _
  obtain ⟨h', hh'⟩ := (Set.ssubset_univ_iff.mp
    (Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt Finset.univ p hp hcard)) |>
      fun h => (Set.ne_univ_iff_exists_notMem _).mp h
  refine ⟨h', fun i hi => ?_⟩
  intro hre
  apply hh'
  refine Set.mem_iUnion₂.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, ?_⟩
  simpa [p] using hre

variable (heig : ∀ i (h : 𝔥), ⁅(h : g), b i⁆ = wt i h • b i) (H : g) (hH : H ∈ 𝔥)
  (hspan : Submodule.span ℂ {Y : g | ∃ k : ℤ, ⁅H, Y⁆ = (k : ℂ) • Y} = ⊤)

omit [Fintype I] in
include heig hspan in
/-- The weights take integral values at the integral grading element `H`. -/
theorem exists_int_wt (i : I) : ∃ n : ℤ, wt i ⟨H, hH⟩ = n := by
  classical
  obtain ⟨t, htS, htspan, hli⟩ :=
    exists_linearIndependent ℂ {Y : g | ∃ k : ℤ, ⁅H, Y⁆ = (k : ℂ) • Y}
  let bH : Module.Basis t ℂ g := Module.Basis.mk hli (by rw [Subtype.range_coe, htspan, hspan])
  have hb (a : t) : bH a = a := Module.Basis.mk_apply _ _ _
  choose d hd using fun a : t => htS a.2
  have h1 := mem_eigenSpan_of_ad bH (fun a => (d a : ℂ)) H (fun a => by rw [hb]; exact hd a)
    (wt i ⟨H, hH⟩) (heig i ⟨H, hH⟩)
  by_contra hno
  push Not at hno
  have hempty : {a : t | (d a : ℂ) = wt i ⟨H, hH⟩} = ∅ := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact fun h => hno (d a) h.symm
  rw [hempty, Set.image_empty, Submodule.span_empty, Submodule.mem_bot] at h1
  exact b.ne_zero i h1

include heig hspan in
/-- **A regular grading element.** There is `H'' ∈ 𝔥` such that the real parts `φ i` of the
weights at `H''` vanish exactly for the weights that vanish, and are positive on every basis
vector whose `H`-eigenvalue is a positive integer. -/
theorem exists_regular :
    ∃ H'' : 𝔥, (∀ i, (wt i H'').re = 0 ↔ wt i = 0) ∧
      ∀ i (n : ℕ), wt i ⟨H, hH⟩ = ((n + 1 : ℕ) : ℂ) → 0 < (wt i H'').re := by
  classical
  obtain ⟨h', hh'⟩ := exists_re_ne_zero (wt := wt)
  choose n hn using exists_int_wt heig H hH hspan
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ i, |(wt i h').re| < N := by
    refine ⟨⌈∑ i, |(wt i h').re|⌉₊ + 1, fun i => ?_⟩
    have h1 : |(wt i h').re| ≤ ∑ i, |(wt i h').re| :=
      Finset.single_le_sum (f := fun i => |(wt i h').re|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ i)
    have h2 := Nat.le_ceil (∑ i, |(wt i h').re|)
    push_cast
    linarith
  refine ⟨(N : ℂ) • ⟨H, hH⟩ + h', fun i => ?_, fun i k hk => ?_⟩
  · have hre : (wt i ((N : ℂ) • ⟨H, hH⟩ + h')).re = N * n i + (wt i h').re := by
      rw [map_add, map_smul, hn, smul_eq_mul, Complex.add_re]
      simp
    constructor
    · intro h0
      by_contra hne
      by_cases hni : n i = 0
      · rw [hre, hni] at h0
        simp only [Int.cast_zero, mul_zero, zero_add] at h0
        exact hh' i hne h0
      · have h3 : (1 : ℝ) ≤ |(n i : ℝ)| := by
          rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hni
        have h4 := hN i
        rw [hre] at h0
        have h5 : |(N : ℝ) * n i| = N * |(n i : ℝ)| := by
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
        have h6 : (N : ℝ) * n i = -(wt i h').re := by linarith
        rw [h6, abs_neg] at h5
        nlinarith [abs_nonneg (wt i h').re]
    · intro h0
      rw [h0]
      simp
  · have hre : (wt i ((N : ℂ) • ⟨H, hH⟩ + h')).re = N * (k + 1) + (wt i h').re := by
      rw [map_add, map_smul, hk, smul_eq_mul, Complex.add_re]
      simp
    rw [hre]
    have h4 := hN i
    have h5 : -(N : ℝ) < (wt i h').re := by
      have := neg_abs_le (wt i h').re
      linarith
    have h6 : (N : ℝ) ≤ N * (k + 1) := by
      have : (1 : ℝ) ≤ k + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    linarith

end Regular

end Langlands.Algebra.ParabolicCenterProjection
