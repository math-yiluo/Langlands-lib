# Krull intersection along the section of a smooth algebra

This helper module of `Langlands.GroupScheme.smoothConnectedNormalizer` proves
a Krull-intersection statement for smooth algebras with a section, without any
Noetherian hypothesis.

## Main result

`exists_mul_eq_zero_of_forall_mem_pow`: let `C` be a smooth `R`-algebra with
an `R`-algebra section `ε : C →ₐ[R] R`. If `b ∈ C` lies in every power
`(ker ε) ^ n`, then there is `s ∈ C` with `ε s = 1` and `s * b = 0`.
Geometrically, a function vanishing to infinite order along the section
vanishes on an open neighbourhood of the section.

## The Noetherian step

`exists_one_sub_smul_eq_zero` treats a Noetherian ring `C₀` over `R₀`, an
ideal `J` of `C₀` with every truncation `C₀ ⧸ J ^ (n + 1)` flat over `R₀`, and
an arbitrary `R₀`-algebra `R`. Suppose `b ∈ C₀ ⊗[R₀] R` vanishes in every
`(C₀ ⧸ J ^ (n + 1)) ⊗[R₀] R`. Then `(1 - r) • b = 0` for some `r ∈ J`.

The proof writes `b` as the image of an element `b'` of `C₀ ⊗[R₀] M`, where `M`
is a finitely generated `R₀`-submodule of `R`. Flatness of the truncations
makes `(C₀ ⧸ J ^ (n + 1)) ⊗[R₀] M → (C₀ ⧸ J ^ (n + 1)) ⊗[R₀] R` injective, so
`b'` vanishes in every truncation. Right exactness of the tensor product puts
`b'` in every `J ^ i • (C₀ ⊗[R₀] M)`. This is a finitely generated module over
the Noetherian ring `C₀`. The Krull intersection theorem
`Ideal.mem_iInf_smul_pow_eq_bot_iff` therefore gives `r ∈ J` with
`r • b' = b'`. Mapping back to `C₀ ⊗[R₀] R` gives the claim.

## Descent to a Noetherian model

For the main result, Mathlib's `Algebra.Smooth.exists_subalgebra_fg` gives a
finitely generated subring `R₀` of `R`, a smooth `R₀`-algebra `C₀` and an
isomorphism `e : R ⊗[R₀] C₀ ≃ C`. Then `R₀` and `C₀` are Noetherian. The
section is not assumed to descend. Instead, `C₀` is used as the new base:

- `ε` restricts to a ring map `ε₀ : C₀ → R`, making `R` a `C₀`-algebra;
- `C₁ = C₀ ⊗[R₀] C₀` is a Noetherian `C₀`-algebra (through the left factor),
  with the multiplication `μ : C₁ → C₀` as a section;
- `C ≃ C₁ ⊗[C₀] R` through `e`, `Algebra.TensorProduct.cancelBaseChange` and
  commutativity, and `ε` corresponds to the base change of `μ`.

`C₁` is smooth over `C₀` as a base change of `C₀`. The Library result
`Algebra.Smooth.finite_projective_quotient_ker_pow` makes every truncation
`C₁ ⧸ (ker μ) ^ (n + 1)` finite projective, and hence flat, over `C₀`. The
kernel of the base change of `μ` is the extension of `ker μ`, by
`Algebra.TensorProduct.rTensor_ker`. So the image of `b` vanishes in every
truncation, and the Noetherian step gives `r ∈ ker μ` killing it via `1 - r`.
The element `s` is the image of `(1 - r) ⊗ 1` in `C`. Then `ε s = μ (1 - r) = 1`
and `s * b = 0`.

## Provenance

This is the Krull-intersection input in the proof of Brian Conrad,
*Reductive group schemes* (2014), Proposition 2.1.6 (printed and one-based
PDF pp.61–63, source `conrad-2014-reductive-group-schemes`). Conrad reduces
to the Noetherian case by approximation and then applies Krull's theorem on a
local ring of `H`. The formal route here is derived for this proof: it descends
only the smooth algebra and uses the diagonal model `C₀ ⊗[R₀] C₀` so that no
section has to descend.
