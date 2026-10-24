# Degree-weighted transfer at finite places

## Definition

Let `L/K` be a finite extension of number fields, and let `A` be any additive
commutative monoid. The fields and `A` may lie in different universes.
`finitePlaceDegreeTransfer` is the additive homomorphism

```
(HeightOneSpectrum (𝓞 K) →₀ A) →+ (HeightOneSpectrum (𝓞 L) →₀ A)
```

which sends a family `f` to the family whose value at an upper finite place
`q` is

```
Module.finrank ((q.under (𝓞 K)).adicCompletion K) (q.adicCompletion L)
  • f (q.under (𝓞 K)).
```

The completion algebra is the actual algebra supplied by the
`FiniteExtension` scope. No Galois hypothesis is imposed. The term
“transfer” here refers to this degree-weighted operation on additive
families; it is not a cohomological corestriction map or an idele norm map.

The construction uses `Finsupp.liftAddHom`. A single value `a` at a base place
`p` is sent to the finite sum, over `q : FinitePlacesAbove L p`, of the single
value `[L_q : K_p] • a` at `q`. Each fiber is finite, so this directly
constructs an upper finitely supported family. It does not assume a support
bound on any unrelated upper family.

## Evaluation and sum laws

- `finitePlaceDegreeTransfer_single` describes the construction on a single
  base place. The next two lemmas compute its value above that place and its
  vanishing above other places.
- `finitePlaceDegreeTransfer_apply` proves the displayed coordinate formula
  by additive induction on the input finitely supported family.
  `finitePlaceDegreeTransfer_apply_of_liesOver` rewrites it using any specified
  lower place `p` with an actual `q.asIdeal.LiesOver p.asIdeal` instance.
- `finiteLocalDegree_sum` proves that the sum of `[L_q : K_p]` over the places
  above `p` equals `[L : K]`. It rewrites each summand using `localDegree_eq`
  and applies `finitePlacesAbove_sum_ramification_inertia`.
- `finitePlaceSum` is the additive sum of a finite-place family. Its single
  evaluation and equality with `∑ᶠ p, f p` are proved.
- `finitePlaceSum_degreeTransfer` and `finsum_finitePlaceDegreeTransfer` prove
  that the sum after degree-weighted transfer is `[L : K]` times the original
  sum. Additive induction reduces the assertion to a single base place;
  distributing scalar multiplication then applies `finiteLocalDegree_sum`.

## Provenance and scope

This is internal derived infrastructure. Its arithmetic inputs are the
existing `LocalDegree` and `FiniteComparisonReduction` results on actual
adic completions and actual primes, together with `Inclusion.liesOver_under`.
Its additive inputs are Mathlib's finite sums and `Finsupp.liftAddHom`.
No new external source claim is introduced.

In the global invariant construction, a future local restriction theorem
can identify the finite invariant vector of a restricted class with this
transfer. This module proves the summation calculation only; it does not
assert that identification, prove local invariant naturality, or prove
`GlobalInvariantStatement`.
