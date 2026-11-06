# Finite-height stability for actual additive-group representations

This is a derived prerequisite for a supplied actual matrix representation
`ρ` of the one-dimensional vector group over a field `k : Type u`, with a
finite decidable coordinate type `n : Type`. No nonemptiness assumption on `n`
is imposed. All nilpotent scalar tests use arbitrary commutative `k`-algebras
in universe `u`, including nonreduced algebras. Neither an infinite field nor
algebraic closedness is assumed.

The representation, its polynomial orbit and its coefficient operators are the
actual constructions in `AdditiveDividedPowers`, `AdditiveFixedVectors` and
`AdditiveInvariantSubspaces`. No abstract family of operators is substituted
for the supplied group action.

## Nilpotent scalar stability

`IsStableAtNilpotentScalars ρ N W` says that, for every test algebra `A`, every
`t : A` with `t ^ N = 0`, every `v ∈ W` and every `k`-linear functional
`ℓ : A → k`, applying `ℓ` coordinatewise to the actual action at the scalar
point `t` gives a vector in `W`. It is the restriction of the existing affine
stability test to these scalar points.

`truncatedCoeff N m` is the linear functional on `AdjoinRoot (X^N)` obtained
by taking the unique monic remainder and then its degree-`m` coefficient.
`root_pow` proves the nilpotence relation for the universal scalar.
`truncatedCoeff_aeval` proves that, for `m < N`, evaluating any polynomial at
that scalar and applying the functional recovers its original degree-`m`
coefficient. The proof applies coefficient extraction to Mathlib's monic
division identity; the term divisible by `X^N` has zero coefficient below N.

`isStableAtNilpotentScalars_iff_invariant_dividedPower` identifies this
stability predicate with
`∀ m < N, ∀ v ∈ W, dividedPower ρ m v ∈ W`. Necessity tests the actual
action in `AdjoinRoot (X^N)` and extracts each coefficient below N.
Sufficiency uses the preceding finite coefficient expansion of an arbitrary
functional applied to the action. Terms with degree at least N vanish because
`t ^ N = 0`; the remaining terms lie in W by coefficient invariance.
This result needs no characteristic hypothesis and includes `N = 0`.

Ordinary all-test stability implies this predicate for every N.
`IsStableAtNilpotentScalars.mono` restricts stability at bound M to any
smaller bound N.

## Bounded fixed subspaces

`IsFixedAtNilpotentScalars ρ N v` says that the actual scalar-extended
vector is fixed at every `N`-nilpotent scalar over every test algebra.
`truncatedFixedSubmodule ρ N` is the intersection of the kernels of
`dividedPower ρ m` over `0 < m < N`.

`mem_truncatedFixedSubmodule_iff_isFixedAtNilpotentScalars` proves these
two descriptions agree. The forward proof shows that each polynomial orbit
coordinate minus the constant original coordinate is divisible by `X^N`,
then evaluates at a scalar killed by its N-th power. The reverse proof tests
the universal scalar and uses `truncatedCoeff` to extract each positive
coefficient below N. Full additive fixed vectors lie in every such bounded
fixed submodule.

## Prime characteristic and finite height

The remaining results assume a natural prime `p` with `CharP k p`.
`dividedPower_mem_of_pPowerOperator_mem_lt` proves that a subalgebra
containing the operators `pPowerOperator ρ p r` for `r < s` contains
`dividedPower ρ m` for every `m < p ^ s`. Its strong induction follows the
existing unbounded coefficient-generation proof: a degree that is a power of p
uses the corresponding generator, whose index is below s; any other positive
degree has a nonzero intermediate binomial coefficient by the proved Lucas
consequence. The divided-power composition law and its invertible binomial
coefficient reduce that degree to two strictly smaller degrees. Both remain
below the same bound.

Applying this to the subalgebra of endomorphisms preserving W proves
`invariant_dividedPower_lt_iff_invariant_pPowerOperator_lt`. Consequently,
`isStableAtNilpotentScalars_iff_invariant_pPowerOperator_lt` identifies
stability at every scalar satisfying `t ^ (p ^ s) = 0` with invariance
under precisely the first s p-power operators.

The bounded fixed-space proof uses the same strong induction and binomial
law, with vanishing of the smaller positive coefficient replacing subalgebra
membership. It gives `mem_truncatedFixedSubmodule_iff_pPowerOperator_lt`
and `isFixedAtNilpotentScalars_iff_pPowerOperator_lt`.
`truncatedFixedSubmodule_eq_iInf_ker_pPowerOperator` expresses the bounded
fixed subspace as the finite intersection over `r : Fin s` of the kernels
of these operators. At height zero the bound is `p ^ 0 = 1`, and the
intersection is the whole space.

Finally, `isStableSubspace_iff_forall_height` and
`isFixedVector_iff_forall_height` recover full additive stability and the
existing fixed-vector predicate from all finite heights. For each index r,
height `r + 1` supplies its p-power operator. The preceding additive
comparisons then give ordinary all-affine-test stability or fixedness on
every relative scheme test, respectively.

## Provenance and scope

This unit is internal derived algebra, not a translation of an external
theorem. Its input is the existing actual polynomial action and divided-power
identities, Mathlib's monic remainder construction and proved Lucas consequence,
and the preceding all-test coefficient comparisons. The new bounded results
are not the earlier unbounded criteria: the degree restriction is essential,
and necessity uses the universal nilpotent algebra rather than the unrestricted
polynomial algebra.

No Frobenius-kernel group scheme or comparison with such a scheme is constructed
here. A single finite height is described only by the stated affine nilpotent
scalar tests. This unit does not construct a generating root family, a
highest-weight or Steinberg module, or the big cell, and does not prove
`SteinbergBigCellStatement`.
