# Invariant anisotropic forms and sums of orthogonal complements

This module contains generic linear algebra used in the proof of
`Langlands.Plancherel.WallUnramifiedTwistSurjectivityStatement`. It is internal,
derived material: elementary facts written for that proof, with no structural
claim taken from a source. Everything lives in the namespace
`Langlands.LinearAlgebra.InvariantFormComplements`.

## Clearing denominators

`exists_nsmul_eq_one_tmul` says that for an abelian group `M`, every
`y : ℚ ⊗[ℤ] M` has a positive natural multiple of the form `1 ⊗ m`. Precisely,
there are `n : ℕ` with `0 < n` and `m : M` such that `(n : ℚ) • y = 1 ⊗ₜ m`.
For a pure tensor `q ⊗ x`, take `n` to be the denominator of `q` and
`m = q.num • x`. For a sum, multiply the two denominators.

## Sums of orthogonal complements

Here `K` is a field, `E` is a `K`-vector space, and `B` is a bilinear form on `E`
that is *anisotropic*: `B x x = 0` implies `x = 0`. "Left-orthogonal" means
`B v s = 0` for all `v ∈ V` and `s ∈ S`.

* `mem_of_forall_apply_eq_zero` (no finite-dimensionality needed): suppose
  `V ⊔ S = ⊤`, `V` is left-orthogonal to `S`, and `z` is left-orthogonal to `S`.
  Then `z ∈ V`. Proof: write `z = v + s` with `v ∈ V` and `s ∈ S`. Then
  `0 = B z s = B v s + B s s = B s s`, so `s = 0`.
* `le_sup_of_anisotropic` (with `E` finite-dimensional): suppose
  `V₁ ⊔ S₁ = ⊤` and `V₂ ⊔ S₂ = ⊤`, each `Vᵢ` is left-orthogonal to `Sᵢ`, `V` is
  left-orthogonal to `S`, and `S₁ ⊓ S₂ ≤ S`. Then `V ≤ V₁ ⊔ V₂`. Proof: an
  anisotropic form makes `x ↦ B x` injective from `E` to its dual, and hence
  bijective, since the two dimensions agree. For `x ∈ V`, the functional `B x`
  vanishes on `S₁ ⊓ S₂`. Mathlib's `Subspace.dualAnnihilator_inf_eq` writes it as
  `f₁ + f₂` with `fᵢ` vanishing on `Sᵢ`. Write `fᵢ = B zᵢ`. The previous lemma
  gives `zᵢ ∈ Vᵢ`, and injectivity gives `x = z₁ + z₂`.

## Invariant forms

Here `E` is a `ℚ`-vector space.

* `apply_eq_zero_of_fixed_of_neg`: if `B (s x) (s y) = B x y` for a linear map `s`,
  with `s v = v` and `s a = -a`, then `B v a = 0`. Indeed `B v a = -B v a`.
* `exists_invariant_anisotropic`: let `ρ : W →* (E ≃ₗ[ℚ] E)` be a representation of
  a finite group `W` on a finite-dimensional `E`. Then some anisotropic bilinear
  form `B` satisfies `B (ρ w x) (ρ w y) = B x y` for all `w`, `x`, `y`.
  Construction: let `B₀` be the standard dot product in a chosen basis, so
  `B₀ x y = ∑ᵢ xᵢ yᵢ`. Average over the group:
  `B x y = ∑_w B₀ (ρ w x) (ρ w y)`. `B x x` is a sum of nonnegative rationals,
  and its `w = 1` term is `B₀ x x`, so `B` is anisotropic. Invariance follows by
  reindexing the sum along `w ↦ w * g`.
