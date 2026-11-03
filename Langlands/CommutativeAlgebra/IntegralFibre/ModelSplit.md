# Taylor coefficients detect elements over a Noetherian model

This module is part of the proof of
`Langlands.CommutativeAlgebra.IntegralFibreProjectivityStatement` (Stacks Project, Tag 05FT).
It works with a Noetherian model and proves local splitting for its base change.

## Setting

- `R₀` is a Noetherian ring.
- `S₀` is a Noetherian, flat `R₀`-algebra with a section `σ₀ : S₀ →ₐ[R₀] R₀`.
- `t₀ : Fin d → S₀` are coordinates with `σ₀ (t₀ i) = 0`, and every truncated Taylor map
  `theta σ₀ t₀ k` (module `Taylor`) is bijective.
- `B` is an `R₀`-algebra.
- `hfib`: for every prime `P` of `B` and every `u : S₀` with `σ₀ u = 1`, multiplication by `u` is
  injective on `S₀ ⊗[R₀] P.ResidueField`. This is `SMulInjOn` from module `Purity`.

## Definitions

`taylorCoeffB σ₀ t₀ hθ α : B ⊗[R₀] S₀ →ₗ[B] B` is the base change of the Taylor coefficient
`taylorCoeff σ₀ t₀ hθ α`.

## Statements

- `exists_prime_comap_eq`: let `N` be a `B`-module, also an `R₀`-module compatibly. If
  `p = {r | r • n = 0}` is prime for some `n : N`, then `p` is the contraction of a prime of `B`.
- `SMulInjOn.residueField_of_comap`: injectivity on the fibre at a prime `P` of `B` implies
  injectivity on the fibre at the contracted prime `p`, since `S₀` is flat.
- `eq_zero_of_taylorCoeff_eq_zero`: let `N` be any `B`-module. If every Taylor coefficient
  `(taylorCoeff α).rTensor N y` of `y ∈ S₀ ⊗[R₀] N` vanishes, then `y = 0`.
- `exists_common_tmul`, `exists_fin_family_mem_span`: finitely many tensors can be written with a
  common finite family of right factors. In a Noetherian module, any family has a finite
  subfamily whose span contains every member.
- `locallySplit_of_model`: `Langlands.CommutativeAlgebra.LocallySplit B (B ⊗[R₀] S₀)`.

## Proofs

For `eq_zero_of_taylorCoeff_eq_zero`, write `y = ∑ sⱼ ⊗ nⱼ`. Let `N₀ ⊆ N` be the finite
`R₀`-submodule spanned by the `nⱼ`, and let `y₀` be the corresponding element of `S₀ ⊗ N₀`. Its
Taylor coefficients vanish because `R₀ ⊗ N₀ → R₀ ⊗ N` is injective. By
`mem_pow_smul_top_of_taylorCoeff`, `y₀` lies in every `J₀^k • ⊤`. Krull's intersection theorem
(`Ideal.mem_iInf_smul_pow_eq_bot_iff`, for the finite `S₀`-module `S₀ ⊗ N₀`) gives `r ∈ J₀` with
`(1 - r) • y₀ = 0`, where `σ₀ (1 - r) = 1`.

Every associated prime of `N₀` is the annihilator of an element of `N`, so it comes from a prime
of `B`. By `hfib` and `SMulInjOn.residueField_of_comap`, the purity lemma
`SMulInjOn.of_associatedPrimes` applies. So `1 - r` acts injectively, and `y₀ = 0`.

For local splitting, write the given elements `xᵢ` of `B ⊗ S₀` with common right factors
`s_m ∈ S₀`. The coefficient vectors `(taylorCoeff α (s_m))_m ∈ R₀^K` span a submodule of a
Noetherian module, so finitely many exponents `α₁, …, α_r` suffice. The functionals are
`taylorCoeffB αⱼ`. Let `C ⊆ B^n` be the span of the vectors `(taylorCoeffB αⱼ (xᵢ))ᵢ`. All
Taylor coefficient vectors lie in `C`. Applying the previous theorem to `N = B^n ⧸ C` shows that
the element `∑ s_m ⊗ (b_{·m})` of `S₀ ⊗ B^n` comes from `S₀ ⊗ C`. Reading off coordinates gives
`xᵢ = ∑ⱼ taylorCoeffB αⱼ (xᵢ) • yⱼ`.

## Provenance

This is internal to the 05FT proof, written by Worker 281. It replaces the completion and
Mittag-Leffler arguments of Stacks Tags 05FS and 05FT by Krull's intersection theorem on a
Noetherian model.
