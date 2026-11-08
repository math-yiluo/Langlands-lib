import Langlands.HarmonicAnalysis.GroupAction
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Exponents, and the weak and positive parts of a coefficient

Waldspurger I.3 defines, for a representation of `M` and a character `χ` of the split centre,
the generalized eigenspace `V_χ` and calls `χ` an exponent when `V_χ ≠ 0`; the weak part of a
constant term (III.3, VI.2) is the part attached to the unitary exponents. This module treats an
abstract commutative group `A` acting through `T : A →* End Y`.

* `jointGenEigenspace T χ`: the joint generalized eigenspace `{y : ∀ a, ∃ k, (T a - χ a)^k y = 0}`.
* `exists_sum_mem_jointGenEigenspace`: a vector of a finite-dimensional `T`-stable subspace is a
  finite sum of joint generalized eigenvectors.
* `map_mul_of_mem_jointGenEigenspace`: the eigenvalue function of a nonzero joint generalized
  eigenvector is multiplicative, and `jointCharacter` packages it as a character `A →* ℂˣ`.
* `aeval_rightFunctions_coefficient`: right translation acts on the coefficient
  `m ↦ λ(J(m) y)` through the action on `y`.
* `exists_weak_positive_decomposition`: the coefficient `m ↦ λ(J(m) y)` splits as `F^w + F^+`,
  where `F^w` is annihilated by a polynomial in the right translation by `j(a₀)` whose roots
  have modulus `1`, and `F^+` by one whose roots have modulus at most `θ < 1`, as soon as every
  non-unitary exponent `χ` has `|χ(a₀)| < 1`.
-/

noncomputable section

namespace Langlands.HarishChandraSchwartz

open Polynomial Langlands.HarmonicAnalysis

section Joint

variable {A : Type*} [CommGroup A] {Y : Type*} [AddCommGroup Y] [Module ℂ Y]

/-- The joint generalized eigenspace `{y : ∀ a, ∃ k, (T(a) - χ(a))^k y = 0}` of a commutative
family `T` for `χ : A → ℂ` (Waldspurger's `V_χ` of I.3, for the action of the split centre). -/
def jointGenEigenspace (T : A →* Module.End ℂ Y) (χ : A → ℂ) : Submodule ℂ Y :=
  ⨅ a, (T a).maxGenEigenspace (χ a)

theorem mem_jointGenEigenspace {T : A →* Module.End ℂ Y} {χ : A → ℂ} {y : Y} :
    y ∈ jointGenEigenspace T χ ↔ ∀ a, ∃ k : ℕ, ((T a - χ a • 1) ^ k) y = 0 := by
  simp [jointGenEigenspace, Module.End.mem_maxGenEigenspace]

theorem commute_jointFamily (T : A →* Module.End ℂ Y) (a b : A) : Commute (T a) (T b) := by
  change T a * T b = T b * T a
  rw [← map_mul, ← map_mul, mul_comm]

theorem commute_jointFamily_sub_smul (T : A →* Module.End ℂ Y) (c d : A) (μ ν : ℂ) :
    Commute (T c - μ • 1) (T d - ν • 1) := by
  have h1 : Commute (T c) (T d - ν • 1) :=
    (commute_jointFamily T c d).sub_right ((Commute.one_right (T c)).smul_right ν)
  have h2 : Commute (μ • (1 : Module.End ℂ Y)) (T d - ν • 1) :=
    (Commute.one_left (T d - ν • 1)).smul_left μ
  exact h1.sub_left h2

/-- A generalized eigenvector gives an eigenvector `(S - μ)^m y` for the same eigenvalue. -/
theorem exists_pow_apply_eigen (S : Module.End ℂ Y) (μ : ℂ) {y : Y} (hy : y ≠ 0) {k : ℕ}
    (hk : ((S - μ • 1) ^ k) y = 0) :
    ∃ m : ℕ, ((S - μ • 1) ^ m) y ≠ 0 ∧
      S (((S - μ • 1) ^ m) y) = μ • ((S - μ • 1) ^ m) y := by
  classical
  have hex : ∃ n : ℕ, ((S - μ • (1 : Module.End ℂ Y)) ^ n) y = 0 := ⟨k, hk⟩
  have hn0 : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0, pow_zero, Module.End.one_apply] at this
    exact hy this
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero hn0
  refine ⟨m, Nat.find_min hex (by omega), ?_⟩
  have h : (S - μ • 1) (((S - μ • 1) ^ m) y) = 0 := by
    rw [← Module.End.mul_apply, ← pow_succ', ← hm]
    exact Nat.find_spec hex
  rw [LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, Module.End.one_apply] at h
  exact h

/-- An eigenvalue of `S` on a generalized `μ`-eigenvector is `μ`. -/
theorem eq_of_apply_eq_smul_of_pow (S : Module.End ℂ Y) {μ ν : ℂ} {w : Y} (hw : w ≠ 0)
    (hS : S w = ν • w) {k : ℕ} (hk : ((S - μ • 1) ^ k) w = 0) : ν = μ := by
  have hpow : ∀ n : ℕ, ((S - μ • 1) ^ n) w = (ν - μ) ^ n • w := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, hS,
        LinearMap.smul_apply, Module.End.one_apply, ← sub_smul, smul_smul, pow_succ]
  rw [hpow k] at hk
  have h := (smul_eq_zero.mp hk).resolve_right hw
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp at h
  · exact sub_eq_zero.mp ((pow_eq_zero_iff hk0.ne').mp h)

/-- `T(b)` preserves the joint generalized eigenspaces. -/
theorem apply_mem_jointGenEigenspace (T : A →* Module.End ℂ Y) {χ : A → ℂ} (b : A) {y : Y}
    (hy : y ∈ jointGenEigenspace T χ) : T b y ∈ jointGenEigenspace T χ := by
  rw [mem_jointGenEigenspace] at hy ⊢
  intro a
  obtain ⟨k, hk⟩ := hy a
  refine ⟨k, ?_⟩
  have hc : Commute ((T a - χ a • 1) ^ k) (T b) :=
    (((commute_jointFamily T a b).sub_left ((Commute.one_left (T b)).smul_left (χ a)))).pow_left k
  rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply, hk, map_zero]

/-- **The eigenvalue function of a nonzero joint generalized eigenvector is multiplicative.** -/
theorem map_mul_of_mem_jointGenEigenspace (T : A →* Module.End ℂ Y) {χ : A → ℂ} {x : Y}
    (hx0 : x ≠ 0) (hx : x ∈ jointGenEigenspace T χ) (a b : A) : χ (a * b) = χ a * χ b := by
  rw [mem_jointGenEigenspace] at hx
  obtain ⟨ka, hka⟩ := hx a
  obtain ⟨m, hw0, hw⟩ := exists_pow_apply_eigen (T a) (χ a) hx0 hka
  set w := ((T a - χ a • 1) ^ m) x with hwdef
  have hwgen : ∀ c : A, ∃ k : ℕ, ((T c - χ c • (1 : Module.End ℂ Y)) ^ k) w = 0 := by
    intro c
    obtain ⟨k, hk⟩ := hx c
    refine ⟨k, ?_⟩
    have hcomm : Commute ((T c - χ c • 1) ^ k) ((T a - χ a • 1) ^ m) :=
      (commute_jointFamily_sub_smul T c a (χ c) (χ a)).pow_pow k m
    rw [hwdef, ← Module.End.mul_apply, hcomm.eq, Module.End.mul_apply, hk, map_zero]
  obtain ⟨kb, hkb⟩ := hwgen b
  obtain ⟨m', hw'0, hw'⟩ := exists_pow_apply_eigen (T b) (χ b) hw0 hkb
  set w' := ((T b - χ b • 1) ^ m') w with hw'def
  have hTa : T a w' = χ a • w' := by
    have hc : Commute (T a) ((T b - χ b • 1) ^ m') :=
      ((commute_jointFamily T a b).sub_right ((Commute.one_right (T a)).smul_right (χ b))).pow_right m'
    rw [hw'def, ← Module.End.mul_apply, hc.eq, Module.End.mul_apply, hw, map_smul]
  obtain ⟨kab, hkab⟩ := hwgen (a * b)
  have hkab' : ((T (a * b) - χ (a * b) • 1) ^ kab) w' = 0 := by
    have hcomm : Commute ((T (a * b) - χ (a * b) • 1) ^ kab) ((T b - χ b • 1) ^ m') :=
      (commute_jointFamily_sub_smul T (a * b) b (χ (a * b)) (χ b)).pow_pow kab m'
    rw [hw'def, ← Module.End.mul_apply, hcomm.eq, Module.End.mul_apply, hkab, map_zero]
  have hTab : T (a * b) w' = (χ a * χ b) • w' := by
    rw [map_mul, Module.End.mul_apply, hw', map_smul, hTa, smul_smul, mul_comm]
  exact (eq_of_apply_eq_smul_of_pow (T (a * b)) hw'0 hTab hkab').symm

theorem map_one_of_mem_jointGenEigenspace (T : A →* Module.End ℂ Y) {χ : A → ℂ} {x : Y}
    (hx0 : x ≠ 0) (hx : x ∈ jointGenEigenspace T χ) : χ 1 = 1 := by
  obtain ⟨k, hk⟩ := (mem_jointGenEigenspace.mp hx) 1
  have hT1 : T 1 x = (1 : ℂ) • x := by rw [map_one, Module.End.one_apply, one_smul]
  exact (eq_of_apply_eq_smul_of_pow (T 1) hx0 hT1 hk).symm

/-- The character `A →* ℂˣ` of a multiplicative `χ : A → ℂ` with `χ(1) = 1`. -/
def jointCharacter (χ : A → ℂ) (h1 : χ 1 = 1) (hmul : ∀ a b, χ (a * b) = χ a * χ b) :
    A →* ℂˣ :=
  MonoidHom.toHomUnits { toFun := χ, map_one' := h1, map_mul' := hmul }

@[simp] theorem jointCharacter_apply (χ : A → ℂ) (h1 : χ 1 = 1)
    (hmul : ∀ a b, χ (a * b) = χ a * χ b) (a : A) : (jointCharacter χ h1 hmul a : ℂ) = χ a :=
  rfl

/-- **Decomposition into joint generalized eigenvectors.** A vector of a finite-dimensional
subspace `W` stable under every `T(a)` is a finite sum of joint generalized eigenvectors lying
in `W`. -/
theorem exists_sum_mem_jointGenEigenspace (T : A →* Module.End ℂ Y) (W : Submodule ℂ Y)
    [FiniteDimensional ℂ W] (hW : ∀ a, ∀ x ∈ W, T a x ∈ W) {y : Y} (hy : y ∈ W) :
    ∃ c : (A → ℂ) →₀ Y, (∀ χ, c χ ∈ W ⊓ jointGenEigenspace T χ) ∧
      (c.sum fun _ x => x) = y := by
  have hmaps : ∀ a, Set.MapsTo (T a) W W := fun a x hx => hW a x hx
  let f : A → Module.End ℂ W := fun a => (T a).restrict (hmaps a)
  have hcomm : Pairwise fun a b => Commute (f a) (f b) := by
    intro a b _
    ext x
    change T a (T b x) = T b (T a x)
    rw [← Module.End.mul_apply, (commute_jointFamily T a b).eq, Module.End.mul_apply]
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    f hcomm fun a => Module.End.iSup_maxGenEigenspace_eq_top (f a)
  have hmem : (⟨y, hy⟩ : W) ∈ ⨆ χ : A → ℂ, ⨅ a, (f a).maxGenEigenspace (χ a) := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨c, hc, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hmem
  refine ⟨c.mapRange W.subtype (map_zero _), fun χ => ?_, ?_⟩
  · rw [Finsupp.mapRange_apply]
    have h := Submodule.inf_iInf_maxGenEigenspace_of_forall_mapsTo (fun a => T a) W hmaps
      (μ := χ)
    change (c χ : Y) ∈ W ⊓ ⨅ a, (T a).maxGenEigenspace (χ a)
    rw [h]
    exact Submodule.mem_map_of_mem (hc χ)
  · rw [Finsupp.sum_mapRange_index (fun _ => rfl), Finsupp.sum]
    have h := congrArg W.subtype hsum
    rw [Finsupp.sum, map_sum] at h
    simpa using h

end Joint

section Coefficient

variable {M : Type*} [Group M] {Y : Type*} [AddCommGroup Y] [Module ℂ Y]

/-- **Right translation acts on a coefficient through the vector.** For a representation `J` of
`M`, a linear form `lam` and `y`, the right translation `ρ(g)` acts on `m ↦ lam (J(m) y)` by
`p(ρ(g))(m ↦ lam (J(m) y)) = m ↦ lam (J(m) (p(J(g)) y))`. -/
theorem aeval_rightFunctions_coefficient (J : Representation ℂ M Y) (lam : Y →ₗ[ℂ] ℂ) (g : M)
    (p : ℂ[X]) (y : Y) :
    aeval (GroupAction.rightFunctions g) p (fun m => lam (J m y)) =
      fun m => lam (J m (aeval (J g) p y)) := by
  funext m
  rw [aeval_eq_sum_range, aeval_eq_sum_range, LinearMap.sum_apply, Finset.sum_apply,
    LinearMap.sum_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply, LinearMap.smul_apply, map_smul, map_smul, ← map_pow,
    GroupAction.rightFunctions_apply, map_mul, Module.End.mul_apply, map_pow]

/-- A product of polynomials, each annihilating one summand, annihilates the sum. -/
theorem aeval_prod_apply_sum_eq_zero {V ι : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) (s : Finset ι) (q : ι → ℂ[X]) (F : ι → V)
    (h : ∀ i ∈ s, aeval T (q i) (F i) = 0) : aeval T (∏ i ∈ s, q i) (∑ i ∈ s, F i) = 0 := by
  classical
  rw [map_sum]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [← Finset.prod_erase_mul s q hi, map_mul, Module.End.mul_apply, h i hi, map_zero]

/-- The roots of `∏_{i ∈ s} (X - c_i)^{k_i}` are among the `c_i`. -/
theorem exists_eq_of_mem_roots_prod {ι : Type*} {s : Finset ι} {c : ι → ℂ} {k : ι → ℕ}
    {z : ℂ} (hz : z ∈ (∏ i ∈ s, (X - C (c i)) ^ k i).roots) : ∃ i ∈ s, z = c i := by
  classical
  have hne : (∏ i ∈ s, (X - C (c i)) ^ k i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (X_sub_C_ne_zero _)
  rw [mem_roots hne, IsRoot.def, eval_prod, Finset.prod_eq_zero_iff] at hz
  obtain ⟨i, hi, h⟩ := hz
  rw [eval_pow, eval_sub, eval_X, eval_C] at h
  refine ⟨i, hi, sub_eq_zero.mp ?_⟩
  rcases Nat.eq_zero_or_pos (k i) with h0 | h0
  · rw [h0, pow_zero] at h
    exact absurd h one_ne_zero
  · exact (pow_eq_zero_iff h0.ne').mp h

variable {A : Type*} [CommGroup A]

/-- **Weak and positive parts of a coefficient.** Let `J` be a representation of `M` on `Y`,
`j : A →* M`, `W` a finite-dimensional subspace stable under every `J(j(a))`, `y ∈ W` and `lam` a
linear form. Then the coefficient `m ↦ lam (J(m) y)` is `F^w + F^+`, where for every `a₀ ∈ A`:

* `F^w` is annihilated by `p_w(ρ(j(a₀)))` for a monic `p_w` whose roots have modulus `1`;
* if every non-unitary `χ : A → ℂ` with a nonzero joint generalized eigenvector in `W` satisfies
  `|χ(a₀)| < 1`, then `F^+` is annihilated by `p_+(ρ(j(a₀)))` for a monic `p_+` whose roots
  have modulus at most some `θ < 1`.

Here `ρ` is the right translation `GroupAction.rightFunctions`. `F^w` is the sum of the
coefficients of the components of `y` for the unitary exponents, `F^+` that for the others. -/
theorem exists_weak_positive_decomposition (J : Representation ℂ M Y) (j : A →* M)
    (W : Submodule ℂ Y) [FiniteDimensional ℂ W] (hW : ∀ a, ∀ x ∈ W, J (j a) x ∈ W) {y : Y}
    (hy : y ∈ W) (lam : Y →ₗ[ℂ] ℂ) :
    ∃ Fw Fp : M → ℂ, (fun m => lam (J m y)) = Fw + Fp ∧
      (∀ a₀ : A, ∃ pw : ℂ[X], pw.Monic ∧ (∀ z ∈ pw.roots, ‖z‖ = 1) ∧
        aeval (GroupAction.rightFunctions (j a₀)) pw Fw = 0) ∧
      (∀ a₀ : A, (∀ χ : A → ℂ, (∃ x ≠ 0, x ∈ W ⊓ jointGenEigenspace (J.comp j) χ) →
          (∃ b, ‖χ b‖ ≠ 1) → ‖χ a₀‖ < 1) →
        ∃ (pp : ℂ[X]) (θ : ℝ), θ < 1 ∧ pp.Monic ∧ (∀ z ∈ pp.roots, ‖z‖ ≤ θ) ∧
          aeval (GroupAction.rightFunctions (j a₀)) pp Fp = 0) := by
  classical
  set T : A →* Module.End ℂ Y := J.comp j with hT
  obtain ⟨c, hc, hsum⟩ := exists_sum_mem_jointGenEigenspace T W hW hy
  set s := c.support with hs
  set U : (A → ℂ) → Prop := fun χ => ∀ a, ‖χ a‖ = 1 with hU
  set F : (A → ℂ) → M → ℂ := fun χ m => lam (J m (c χ)) with hF
  refine ⟨∑ χ ∈ s.filter U, F χ, ∑ χ ∈ s.filter (fun χ => ¬ U χ), F χ, ?_, ?_, ?_⟩
  · rw [Finset.sum_filter_add_sum_filter_not]
    funext m
    rw [Finset.sum_apply]
    conv_lhs => rw [← hsum]
    rw [Finsupp.sum, map_sum, map_sum]
  · -- the weak part
    intro a₀
    have hk : ∀ χ : A → ℂ, ∃ k : ℕ,
        ((T a₀ - χ a₀ • (1 : Module.End ℂ Y)) ^ k) (c χ) = 0 := fun χ =>
      (mem_jointGenEigenspace.mp (hc χ).2) a₀
    choose k hk using hk
    refine ⟨∏ χ ∈ s.filter U, (X - C (χ a₀)) ^ k χ,
      monic_prod_of_monic _ _ fun χ _ => (monic_X_sub_C _).pow _, fun z hz => ?_, ?_⟩
    · obtain ⟨χ, hχ, rfl⟩ := exists_eq_of_mem_roots_prod hz
      exact (Finset.mem_filter.mp hχ).2 a₀
    · refine aeval_prod_apply_sum_eq_zero _ _ _ _ fun χ _ => ?_
      rw [hF, aeval_rightFunctions_coefficient]
      have e : aeval (J (j a₀)) ((X - C (χ a₀)) ^ k χ) (c χ) = 0 := by
        rw [map_pow, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
        exact hk χ
      funext m
      rw [e, map_zero, map_zero, Pi.zero_apply]
  · -- the positive part
    intro a₀ hstrict
    have hk : ∀ χ : A → ℂ, ∃ k : ℕ,
        ((T a₀ - χ a₀ • (1 : Module.End ℂ Y)) ^ k) (c χ) = 0 := fun χ =>
      (mem_jointGenEigenspace.mp (hc χ).2) a₀
    choose k hk using hk
    set sp := s.filter (fun χ => ¬ U χ) with hsp
    have hlt : ∀ χ ∈ sp, ‖χ a₀‖ < 1 := by
      intro χ hχ
      obtain ⟨hχs, hχU⟩ := Finset.mem_filter.mp hχ
      refine hstrict χ ⟨c χ, Finsupp.mem_support_iff.mp hχs, hc χ⟩ ?_
      by_contra hall
      push Not at hall
      exact hχU hall
    refine ⟨∏ χ ∈ sp, (X - C (χ a₀)) ^ k χ, ((sp.sup fun χ => ‖χ a₀‖₊ : NNReal) : ℝ), ?_,
      monic_prod_of_monic _ _ fun χ _ => (monic_X_sub_C _).pow _, fun z hz => ?_, ?_⟩
    · have h : (sp.sup fun χ => ‖χ a₀‖₊) < 1 := by
        rw [Finset.sup_lt_iff (by norm_num)]
        intro χ hχ
        have := hlt χ hχ
        rw [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]
        exact this
      exact_mod_cast h
    · obtain ⟨χ, hχ, rfl⟩ := exists_eq_of_mem_roots_prod hz
      have := Finset.le_sup (f := fun χ => ‖χ a₀‖₊) hχ
      rw [← NNReal.coe_le_coe, coe_nnnorm] at this
      exact this
    · refine aeval_prod_apply_sum_eq_zero _ _ _ _ fun χ _ => ?_
      rw [hF, aeval_rightFunctions_coefficient]
      have e : aeval (J (j a₀)) ((X - C (χ a₀)) ^ k χ) (c χ) = 0 := by
        rw [map_pow, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
        exact hk χ
      funext m
      rw [e, map_zero, map_zero, Pi.zero_apply]

end Coefficient

end Langlands.HarishChandraSchwartz
