# A unique-factorization criterion from one factorial chart

This module proves a commutative-algebra criterion for unique factorization,
`uniqueFactorizationMonoid_of_chart`, with some small helper lemmas. It is
written to prove that the coordinate ring of a split simply connected group is
factorial (`SplitSimplyConnectedFactorialStatement`). There the chart is the
coordinate ring of the big cell, and the primes `p i` are the boundary
divisors. The criterion itself is pure commutative algebra and mentions no
group schemes.

## Setting

Throughout, `A` is an integral domain with fraction field `K`
(`IsFractionRing A K`).

- `loc K p` is the localization `A_p`, viewed as an `A`-subalgebra of `K`.
- For an `A`-subalgebra `S` of `K` and a prime `Q` of `S`, `chartLoc K S Q` is
  the localization `S_Q` inside `K`.
- `IsChart S` says that `S_Q = A_{Q ∩ A}` inside `K` for every prime `Q` of
  `S`. This is the algebraic content of an open immersion `Spec S → Spec A` of
  integral schemes with the same function field: the local rings agree.

## Helper lemmas

- `mem_loc`: membership in `A_p` means being a fraction `a / s` with `s ∉ p`.
- `algebraMap_mem_loc`: elements of `A` lie in every `A_p`.
- `inv_algebraMap_notMem_loc`: if `a ∈ p` is nonzero, then `1/a ∉ A_p`.
- `mem_loc_of_mem_chart`: elements of a chart `S` lie in `A_{Q ∩ A}` for every
  prime `Q` of `S`.
- `height_comap_eq`: for a chart, `ht(Q ∩ A) = ht(Q)`. The two localizations
  are equal subrings of `K`, so they have the same Krull dimension.
  `IsLocalization.AtPrime.ringKrullDim_eq_height` identifies these dimensions
  with the heights.
- `zpow_mem`, `zpow_mem_of_nonneg`, `unit_mul`, `unit_prod`: integer powers and
  finite products of elements that are invertible in a subalgebra.

## The criterion

`uniqueFactorizationMonoid_of_chart` assumes the following:

- `A` is Noetherian and integrally closed;
- `S` is a chart of `A` and a unique factorization monoid;
- `r` is a finite index type, and for each `i` there are `f i ∈ K` and a prime
  `p i` of `A` such that:
  - `f i` and `(f i)⁻¹` lie in `S`;
  - `f i ∈ A_{p i}` and `(f i)⁻¹ ∉ A_{p i}`;
  - every nonzero `x ∈ K` is `f i ^ n` times a unit of `A_{p i}` for some
    integer `n`. With the previous condition this says `A_{p i}` is a discrete
    valuation ring with uniformizer `f i`;
  - for `j ≠ i`, `f j` is a unit of `A_{p i}`;
- every height-one prime of `A` is the contraction of a prime of `S` or equals
  some `p i`.

The conclusion is `UniqueFactorizationMonoid A`.

## Proof

1. **Krull property.** If `x ∈ K` lies in `A_q` for every height-one prime `q`,
   then `x ∈ A`. This is
   `IsIntegrallyClosed.exists_algebraMap_eq_of_forall_height_eq_one`, from the
   Library's AnthropicFLT port, for Noetherian integrally closed domains.
2. **Membership test.** If `x ∈ S` and `x ∈ A_{p i}` for all `i`, then `x ∈ A`.
   By exhaustion, every height-one prime either comes from `S`, and then
   `mem_loc_of_mem_chart` applies, or is some `p i`.
3. **Mathlib criterion.** By
   `UniqueFactorizationMonoid.of_forall_isPrincipal_of_height_eq_one`, it
   suffices to show that every height-one prime `q` of `A` is principal.
4. **Primes from the chart.** Suppose `q = Q ∩ A`. Then `ht Q = 1` by
   `height_comap_eq`, so `Q = (π)` because `S` is factorial. Write `n i` for the
   valuation of `π` at `p i`, and put `u = ∏ f i ^ (-n i)`, a unit of `S`. Then
   `π u` is a unit at every `p j`. By step 2, `π u = a` for some `a ∈ A`, and
   one checks `q = (a)`:
   - `a ∈ q` because `a = u π ∈ Q`.
   - If `b ∈ q`, then `b = s π` with `s ∈ S`. Step 2 applies to `s u⁻¹ = b / a`,
     so `b / a ∈ A`.
5. **The primes `p i`.** By step 2, `f i = a` for some `a ∈ A`, and `a ∈ p i`
   because `(f i)⁻¹ ∉ A_{p i}`. If `b ∈ p i` is nonzero, its valuation `n` at
   `p i` is at least one: otherwise `1/b` would lie in `A_{p i}`. So
   `b / f i ∈ A_{p i}`. At `p j` with `j ≠ i`, `b / f i` lies in `A_{p j}`
   because `f i` is a unit there. Also `b / f i ∈ S`. Step 2 gives
   `b / a ∈ A`, so `p i = (a)`.

## Status

The Lean file compiles with no errors, no warnings and no proof holes. Nothing
in it depends on group schemes.
