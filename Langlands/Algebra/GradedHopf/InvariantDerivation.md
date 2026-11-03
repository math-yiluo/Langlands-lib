# Invariant derivations of a polynomial bialgebra

Author: Worker 1389 designed and implemented this module and wrote this note, as
part of task `90ffbd89-a3dd-4baa-84ba-332896bbbd17` (split unipotence from the
absence of zero Lie weights). No other worker's draft was reused. Provenance: internal.
This is the standard construction of left-invariant vector fields from tangent vectors at
the identity, written for a bialgebra `A` whose underlying algebra is a polynomial algebra.
It is used in `Langlands.Algebra.GradedHopf.Primitive` for Lemma A.

Throughout, `k` is a commutative ring, `A` a commutative `k`-bialgebra, and `z : σ → A`
a family with `hz : Function.Bijective (MvPolynomial.aeval z)`, i.e. polynomial
coordinates. The counit is not required to vanish on `z`.

## Counit identity

`sum_counit_right_smul_left`: for any representation `comul a = ∑ aᵢ ⊗ bᵢ` (Mathlib's
`Coalgebra.Repr`), `∑ counit bᵢ • aᵢ = a`. It is the right counit axiom pushed through
`TensorProduct.rid`.

## Coordinates and partial derivatives

- `coordEquiv hz : MvPolynomial σ k ≃ₐ[k] A` is the isomorphism `aeval z`. `coordEquiv_X`
  says that it sends `X i` to `z i`.
- `coordDeriv hz i : Derivation k A A` is the partial derivative `∂/∂zᵢ`, i.e. Mathlib's
  `pderiv i` transported along `coordEquiv hz` (`coordDeriv_apply`).
  `coordDeriv_z`: `∂zⱼ/∂zᵢ` is `1` if `j = i` and `0` otherwise.
- `adjoin_range_eq_top`: the `z i` generate `A`.
- `derivation_sum_apply`: a finite sum of derivations is evaluated termwise.
- `derivation_eq_sum` (chain rule): for any `D : Derivation k A A` and `σ` finite,
  `D a = ∑ j, D (z j) * ∂a/∂zⱼ`. Both sides are derivations agreeing on the generators
  (Mathlib's `Derivation.ext_of_adjoin_eq_top`).

## Tangent vectors at the counit

- `coordTangent hz i : A →ₗ[k] k` is `counit ∘ ∂/∂zᵢ`.
- `coordTangent_mul`: `ξ(ab) = ε(a) ξ(b) + ε(b) ξ(a)`, where `ξ = coordTangent hz i` and
  `ε` is the counit. Also `coordTangent_one`: `ξ 1 = 0`.
- `coordTangent_z`: `ξᵢ (z j)` is `1` if `j = i` and `0` otherwise.
- `coordTangent_eq_zero_of_mem_sq`: `ξᵢ` vanishes on the square of the augmentation ideal
  `RingHom.ker (Bialgebra.counitAlgHom k A)`.

## Invariant derivations

- `invariantDerivLinear hz i : A →ₗ[k] A` is
  `TensorProduct.rid ∘ (id ⊗ ξᵢ) ∘ comul`, i.e. `a ↦ ∑ a₁ ξᵢ(a₂)`.
  `invariantDerivLinear_repr` computes it on any representation of `comul a`.
- `invariantDerivLinear_mul`: it satisfies the Leibniz rule
  `δ(ab) = a δ(b) + b δ(a)`. The proof uses `comul (ab) = comul a * comul b`,
  `coordTangent_mul` and `sum_counit_right_smul_left` termwise.
- `invariantDeriv hz i : Derivation k A A` packages it (`invariantDeriv_apply`).
- `counit_invariantDeriv`: `ε (δᵢ a) = ξᵢ a` (left counit axiom
  `Coalgebra.sum_counit_smul`).
- `invariantDeriv_of_isPrimitiveElem`: for primitive `f`, `δᵢ f = ξᵢ(f) · 1`.

## Primitive elements in the square of the augmentation ideal

`coordDeriv_eq_zero_of_mem_sq`: let `σ` be finite and `A` a domain. If `f` is primitive
(Mathlib's `Bialgebra.IsPrimitiveElem k f`) and lies in the square of the augmentation
ideal, then `∂f/∂zⱼ = 0` for every `j`. Proof as implemented:

- `δᵢ f = ξᵢ(f) · 1 = 0` for all `i`.
- By the chain rule, `0 = δᵢ f = ∑ⱼ N i j * ∂f/∂zⱼ` with `N i j = δᵢ (z j)`.
- The counit of `N` is the identity matrix (`counit_invariantDeriv`, `coordTangent_z`), so
  the counit of `det N` is `1` (`RingHom.map_det`) and `det N ≠ 0`.
- Multiplying `N *ᵥ v = 0` by the adjugate gives `det N • v = 0`, hence `v = 0` because
  `A` is a domain.

`pderiv_eq_zero_of_mem_sq` states the same for the polynomial
`(coordEquiv hz).symm f`: all its partial derivatives vanish.
