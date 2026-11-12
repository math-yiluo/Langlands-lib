# Unitarity of finite-index induction

Author: Worker 5134. Module `Langlands.Weil.Representation.UnitaryInduction`,
namespace `Langlands.FiniteRepresentation` (coset lemmas in
`Langlands.FiniteRepresentation.Induction`). Universes: `uG` (the group `G`),
`uH` (the source group of `induceAlong`), `uV` (the carrier of the induced
representation `A`).

Setting: `G` is a group and `S` a subgroup of finite index. `A` is a
finite-dimensional complex representation of `S`. `induce S A` is the Library's
finite-index induction. Its carrier is the space of functions `f : G → A` with
`f (s * x) = A s (f x)`, and `G` acts by right translation:
`(g · f) x = f (x * g)`. Right cosets `S x` form the type `Induction.Cosets S`,
and `q.out` is the chosen representative of a coset `q`. The predicate
`IsUnitary` asks for a positive definite Hermitian inner product
(`InnerProductSpace.Core ℂ`) invariant under the action.

This is the standard fact that induction from a finite-index subgroup preserves
unitarity. It has no specific literature source here and is used to show that
Henniart's representations `S(X)` (Henniart 2000, §3.4) are unitary.

## Definition: `inducedInnerCore`

Given an inner product `h` on `A`, `inducedInnerCore S A h` is the inner product
on `induce S A` defined by

```
⟪f, f'⟫ = ∑ q : Cosets S, h.inner (f q.out) (f' q.out)
```

Hermitian symmetry, positivity, additivity and conjugate linearity in the first
argument hold term by term. Definiteness: if `⟪f, f⟫ = 0`, every summand has
real part zero, since the real parts are nonnegative and sum to zero. Each
summand is real by Hermitian symmetry, so it is zero, and `f q.out = 0` for all
`q` by definiteness of `h`. Every value `f x` is `A s (f q.out)` for some
`s ∈ S` and coset `q`, so `f = 0`.

## Results

- `Induction.coset_out_mul_injective` and `Induction.coset_out_mul_bijective`:
  for `g ∈ G` the map `q ↦ S (q.out * g)` on right cosets is injective, hence
  bijective, because there are finitely many cosets.
- `Induction.val_eq_factor`: `f x = A (factor S x) (f (coset S x).out)`, where
  `x = factor S x * (coset S x).out` (Library `Induction.factor_mul_out`).
- `inducedInnerCore_inner`: the defining formula.
- `inducedInnerCore_invariant`: if `h` is invariant under `S`, then
  `inducedInnerCore S A h` is invariant under `G`.
- `isUnitary_induce`: if `A` is unitary, so is `induce S A`.
- `isUnitary_induceAlong`: if `A` is unitary and `ι : H →* G` is injective with
  finite-index range, then `induceAlong ι hι A` is unitary.
- `characterLine_isUnitary`: if `‖χ g‖ = 1` for all `g`, the character line
  `characterLine χ` is unitary.

## Proofs

`inducedInnerCore_invariant`. The inner product of `g · f` and `g · f'` is
`∑_q h.inner (f (q.out * g)) (f' (q.out * g))`. By `val_eq_factor` each value
is `A s` applied to the value at the representative of `S (q.out * g)`, with the
same `s` for `f` and `f'`. Invariance of `h` removes `A s`. Reindexing the sum
by the bijection `q ↦ S (q.out * g)` (`Function.Bijective.sum_comp`) gives
`⟪f, f'⟫`.

`isUnitary_induceAlong` holds because `induceAlong ι hι A` is by definition
`induce ι.range (restrict (rangeInverse ι hι) A)`. Restriction preserves
unitarity (Library `isUnitary_restrict`).

`characterLine_isUnitary` transfers along `characterLineEquiv` to the scalar
model on `ℂ`, which carries the standard inner product. There the action
multiplies by `χ g`, and `conj (χ g) * χ g = ‖χ g‖² = 1` (`Complex.conj_mul'`).
