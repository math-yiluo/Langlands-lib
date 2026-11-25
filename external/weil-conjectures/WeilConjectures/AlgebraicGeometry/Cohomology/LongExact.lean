/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import WeilConjectures.AlgebraicGeometry.Cohomology.Exact

/-!
# The long exact cohomology sequence and additivity of the Euler characteristic

A short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of sheaves of modules on a scheme `X` has a long
exact sequence in the cohomology `AlgebraicGeometry.Scheme.Modules.H`. Its connecting maps
`δ : H^n(M₃) ⟶ H^{n+1}(M₁)` are linear over the global functions `Γ(X, 𝒪_X)`, by naturality of
the extension class of the sequence. Over a field `k`, alternating sums of dimensions along the
long exact sequence give the additivity `χ(M₂) = χ(M₁) + χ(M₃)` of the Euler characteristic.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.H.δ`: the connecting map of the long exact sequence.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.H.injective_map_zero_of_shortExact`,
  `AlgebraicGeometry.Scheme.Modules.H.ker_map_g_eq_range_map_f`,
  `AlgebraicGeometry.Scheme.Modules.H.ker_δ_eq_range_map_g`,
  `AlgebraicGeometry.Scheme.Modules.H.ker_map_f_eq_range_δ`: exactness of the long exact sequence.
- `AlgebraicGeometry.Scheme.Modules.eulerChar_eq_add_of_shortExact`: the Euler characteristic is
  additive in short exact sequences of modules with finite-dimensional cohomology vanishing in
  large degrees.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--1`)
-/

@[expose] public section

universe u

open CategoryTheory Limits Abelian

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {S : ShortComplex X.Modules}

/-- The image of a short exact sequence of `𝒪_X`-modules among abelian sheaves is short exact,
since `SheafOfModules.toSheaf` is exact. -/
lemma shortExact_map_toSheaf (hS : S.ShortExact) : (S.map (toAb X)).ShortExact :=
  hS.map_of_exact (toAb X)

/-- The map induced on cohomology by `φ : M ⟶ N` is composition with the degree-`0` class of
`φ`. -/
lemma H.map_apply_eq_comp {M N : X.Modules} (φ : M ⟶ N) (n : ℕ) (z : M.H n) :
    H.map φ n z = Ext.comp (Y := (toAb X).obj M) z (Ext.mk₀ ((toAb X).map φ)) (add_zero n) :=
  rfl

/-- Multiplication by a global function `a` on `H^n(X, M)` is the map induced on cohomology by
multiplication by `a` on `M`. -/
lemma smul_H_eq_map (M : X.Modules) (n : ℕ) (a : Γ(X, ⊤)) (z : M.H n) :
    a • z = H.map (M.smulHom a) n z :=
  rfl

/-- The connecting map `δ : H^n(M₃) ⟶ H^{n+1}(M₁)` of the long exact cohomology sequence of a short
exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0`: composition with its extension class. -/
noncomputable def H.δ (hS : S.ShortExact) (n : ℕ) : S.X₃.H n →+ S.X₁.H (n + 1) :=
  (shortExact_map_toSheaf hS).extClass.postcomp _ rfl

lemma H.δ_apply (hS : S.ShortExact) (n : ℕ) (z : S.X₃.H n) :
    H.δ hS n z = Ext.comp (Y := (toAb X).obj S.X₃) z (shortExact_map_toSheaf hS).extClass rfl :=
  rfl

/-- The connecting map is linear over the global functions: multiplication by `a : Γ(X, 𝒪_X)`
is an endomorphism of the short exact sequence, and the extension class is natural. -/
lemma H.δ_smul (hS : S.ShortExact) (n : ℕ) (a : Γ(X, ⊤)) (z : S.X₃.H n) :
    H.δ hS n (a • z) = a • H.δ hS n z := by
  let φ : S ⟶ S :=
    { τ₁ := S.X₁.smulHom a
      τ₂ := S.X₂.smulHom a
      τ₃ := S.X₃.smulHom a
      comm₁₂ := smulHom_naturality S.f a
      comm₂₃ := smulHom_naturality S.g a }
  have h : (shortExact_map_toSheaf hS).extClass.comp (Ext.mk₀ ((toAb X).map (S.X₁.smulHom a)))
      (add_zero 1) =
      (Ext.mk₀ ((toAb X).map (S.X₃.smulHom a))).comp (shortExact_map_toSheaf hS).extClass
      (zero_add 1) :=
    have hS' := shortExact_map_toSheaf hS
    let φ' : S.map (toAb X) ⟶ S.map (toAb X) := (toAb X).mapShortComplex.map φ
    ShortComplex.ShortExact.extClass_naturality hS' hS' φ'
  rw [smul_H_eq_map, smul_H_eq_map, H.δ_apply, H.δ_apply, H.map_apply_eq_comp,
    H.map_apply_eq_comp, Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero, h]

/-- **Left exactness of `H⁰`.** For a monomorphism `M₁ ⟶ M₂`, the map `H⁰(M₁) ⟶ H⁰(M₂)` is
injective. -/
lemma H.injective_map_zero_of_shortExact (hS : S.ShortExact) :
    Function.Injective (H.map S.f 0) :=
  have : Mono ((toAb X).map S.f) := (shortExact_map_toSheaf hS).mono_f
  Ext.postcomp_mk₀_injective_of_mono _ ((toAb X).map S.f)

/-- Exactness of `H^n(M₁) ⟶ H^n(M₂) ⟶ H^n(M₃)`. -/
lemma H.ker_map_g_eq_range_map_f (hS : S.ShortExact) (n : ℕ) :
    (H.map S.g n).ker = (H.map S.f n).range := by
  ext x
  refine ⟨fun hx ↦ ?_, ?_⟩
  · have hS' := shortExact_map_toSheaf hS
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₂ _ hS' x hx
    exact ⟨y, hy⟩
  · rintro ⟨y, rfl⟩
    rw [AddMonoidHom.mem_ker, ← H.map_comp_apply, S.zero, H.map_zero_apply]

/-- Exactness of `H^n(M₂) ⟶ H^n(M₃) ⟶ H^{n+1}(M₁)`. -/
lemma H.ker_δ_eq_range_map_g (hS : S.ShortExact) (n : ℕ) :
    (H.δ hS n).ker = (H.map S.g n).range := by
  ext x
  refine ⟨fun hx ↦ ?_, ?_⟩
  · have hS' := shortExact_map_toSheaf hS
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ _ hS' x rfl hx
    exact ⟨y, hy⟩
  · rintro ⟨y, rfl⟩
    have h0 : (Ext.mk₀ ((toAb X).map S.g)).comp (shortExact_map_toSheaf hS).extClass
        (zero_add 1) = 0 :=
      (shortExact_map_toSheaf hS).comp_extClass
    rw [AddMonoidHom.mem_ker, H.δ_apply, H.map_apply_eq_comp, Ext.comp_assoc_of_second_deg_zero,
      h0, Ext.comp_zero]

/-- Exactness of `H^n(M₃) ⟶ H^{n+1}(M₁) ⟶ H^{n+1}(M₂)`. -/
lemma H.ker_map_f_eq_range_δ (hS : S.ShortExact) (n : ℕ) :
    (H.map S.f (n + 1)).ker = (H.δ hS n).range := by
  ext x
  refine ⟨fun hx ↦ ?_, ?_⟩
  · have hS' := shortExact_map_toSheaf hS
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ _ hS' x hx rfl
    exact ⟨y, hy⟩
  · rintro ⟨y, rfl⟩
    have h0 : (shortExact_map_toSheaf hS).extClass.comp (Ext.mk₀ ((toAb X).map S.f))
        (add_zero 1) = 0 :=
      (shortExact_map_toSheaf hS).extClass_comp
    rw [AddMonoidHom.mem_ker, H.δ_apply, H.map_apply_eq_comp, Ext.comp_assoc_of_third_deg_zero,
      h0, Ext.comp_zero]

section Field

variable (k : Type u) [Field k] [X.Over (Spec (.of k))]

/-- The connecting map as a `k`-linear map. -/
noncomputable def H.δLinearMap (hS : S.ShortExact) (n : ℕ) : S.X₃.H n →ₗ[k] S.X₁.H (n + 1) where
  toFun := H.δ hS n
  map_add' := map_add _
  map_smul' c := H.δ_smul hS n (globalSectionsRingHom k c)

/-- **Additivity of the Euler characteristic.** Let `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` be a short exact
sequence of `𝒪_X`-modules on a `k`-scheme `X` whose cohomology groups are finite-dimensional and
vanish in degrees above `N`. Then `χ(M₂) = χ(M₁) + χ(M₃)`.

Write `a_q`, `b_q` and `c_q` for the ranks of `H^q(M₁) ⟶ H^q(M₂)`, `H^q(M₂) ⟶ H^q(M₃)` and
`δ : H^q(M₃) ⟶ H^{q+1}(M₁)`. Exactness of the long exact sequence gives `h^q(M₁) = c_{q-1} + a_q`,
`h^q(M₂) = a_q + b_q` and `h^q(M₃) = b_q + c_q`, and the alternating sum of
`h^q(M₂) - h^q(M₁) - h^q(M₃) = -(c_{q-1} + c_q)` telescopes to `± c_N = 0`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--1`) -/
theorem eulerChar_eq_add_of_shortExact (hS : S.ShortExact) (N : ℕ)
    [∀ q, FiniteDimensional k (S.X₁.H q)] [∀ q, FiniteDimensional k (S.X₂.H q)]
    [∀ q, FiniteDimensional k (S.X₃.H q)]
    (h₁ : ∀ q, N < q → Subsingleton (S.X₁.H q)) (h₂ : ∀ q, N < q → Subsingleton (S.X₂.H q))
    (h₃ : ∀ q, N < q → Subsingleton (S.X₃.H q)) :
    S.X₂.eulerChar k = S.X₁.eulerChar k + S.X₃.eulerChar k := by
  let f q := H.mapLinearMap k S.f q
  let g q := H.mapLinearMap k S.g q
  let d q := H.δLinearMap k hS q
  let a q : ℤ := Module.finrank k (LinearMap.range (f q))
  let b q : ℤ := Module.finrank k (LinearMap.range (g q))
  let c q : ℤ := Module.finrank k (LinearMap.range (d q))
  have hker_g q : LinearMap.ker (g q) = LinearMap.range (f q) := by
    ext x
    exact SetLike.ext_iff.mp (H.ker_map_g_eq_range_map_f hS q) x
  have hker_d q : LinearMap.ker (d q) = LinearMap.range (g q) := by
    ext x
    exact SetLike.ext_iff.mp (H.ker_δ_eq_range_map_g hS q) x
  have hker_f q : LinearMap.ker (f (q + 1)) = LinearMap.range (d q) := by
    ext x
    exact SetLike.ext_iff.mp (H.ker_map_f_eq_range_δ hS q) x
  have hker_f₀ : LinearMap.ker (f 0) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (H.injective_map_zero_of_shortExact hS)
  have e₂ q : (S.X₂.finrankH k q : ℤ) = a q + b q := by
    have := LinearMap.finrank_range_add_finrank_ker (g q)
    rw [hker_g] at this
    simp only [finrankH, a, b]
    omega
  have e₃ q : (S.X₃.finrankH k q : ℤ) = b q + c q := by
    have := LinearMap.finrank_range_add_finrank_ker (d q)
    rw [hker_d] at this
    simp only [finrankH, b, c]
    omega
  have e₁ q : (S.X₁.finrankH k (q + 1) : ℤ) = c q + a (q + 1) := by
    have := LinearMap.finrank_range_add_finrank_ker (f (q + 1))
    rw [hker_f] at this
    simp only [finrankH, a, c]
    omega
  have e₁₀ : (S.X₁.finrankH k 0 : ℤ) = a 0 := by
    have := LinearMap.finrank_range_add_finrank_ker (f 0)
    rw [hker_f₀, finrank_bot] at this
    simp only [finrankH, a]
    omega
  have hcN : c N = 0 := by
    have := h₁ (N + 1) (by omega)
    simp only [c, Module.finrank_zero_of_subsingleton, Nat.cast_zero]
  -- the alternating sum of `h^q(M₂) - h^q(M₁) - h^q(M₃)` telescopes
  have key (M : ℕ) : ∑ q ∈ Finset.range (M + 1), (-1 : ℤ) ^ q *
      ((S.X₂.finrankH k q : ℤ) - S.X₁.finrankH k q - S.X₃.finrankH k q) = -(-1) ^ M * c M := by
    induction M with
    | zero => simp [e₁₀, e₂, e₃]
    | succ M ih =>
      rw [Finset.sum_range_succ, ih, e₁, e₂, e₃, pow_succ]
      ring
  have hsupp (M : X.Modules) (hM : ∀ q, N < q → Subsingleton (M.H q)) :
      (Function.support fun q : ℕ ↦ (-1 : ℤ) ^ q * (M.finrankH k q : ℤ)) ⊆
        (Finset.range (N + 1) : Set ℕ) := by
    intro q hq
    by_contra hqN
    have : N < q := by simpa using hqN
    have := hM q this
    exact hq (by simp [finrankH, Module.finrank_zero_of_subsingleton])
  simp only [eulerChar]
  rw [finsum_eq_sum_of_support_subset _ (hsupp _ h₁),
    finsum_eq_sum_of_support_subset _ (hsupp _ h₂), finsum_eq_sum_of_support_subset _ (hsupp _ h₃)]
  have := key N
  rw [hcN, mul_zero] at this
  simp only [mul_sub, Finset.sum_sub_distrib] at this
  linarith

end Field

end AlgebraicGeometry.Scheme.Modules
