# Unconditional positive and norm-one adelic decomposition target

Author: Worker 112.

`HasPositiveNormOneDecomposition F G T i` is the proposition that there
exists a continuous group equivalence

`intrinsicSubgroup F T × normOneSubgroup F G ≃ₜ* AdelicGroupPoints F G`

whose value on every pair `(a,n)` is exactly
`positivePointMap F G T i a * n`. The group law on the source is the
ordinary direct product law. The first factor is the existing intrinsic
positive subgroup of the actual adelic points of `T`; it has not been
replaced by a coordinate vector space. The second factor is the existing
intersection of the normalized idele-norm kernels of all actual
`F`-rational algebraic characters. Both factors and the ambient group
retain their existing topologies. The exact representative formula
prevents an unrelated equivalence of carriers from satisfying this
predicate.

`AdelicPositiveDecompositionStatement` asserts that every connected
reductive group scheme over every number field, with the explicit affine
and locally finite type interfaces, admits a commutative group scheme `T`
and morphism `i : T.toGrp → G` which is an actual split component and
satisfies that predicate. `IsSplitComponent` is the imported algebraic
condition of maximality among central closed split subtori. Its
centrality is tested on every scheme over the base. The torus, its
inclusion and the continuous group equivalence are all in the conclusion.
Neither a splitting isomorphism nor injective finite-index restriction
of rational characters is a premise. All number fields, nonsplit and
anisotropic groups, and split rank zero are included.

Both declarations are definitions returning `Prop`. This file proves no
existence or decomposition assertion.

## Internal provenance and proof boundary

This is a derived target assembling the existing algebraic
`SplitComponentStatement` and `CharacterRestrictionStatement` with the
actual construction `PositiveRealTorus.normOneDecompositionMulEquiv` in
`AdelicNormOneDecomposition`. The latter constructs multiplication and
its inverse from a splitting of `T`, centrality, and injective
finite-index restriction of rational characters. It uses the actual
character logarithm and positive exponential; the inverse removes the
positive factor from the original adelic point.

The algebraic split-component existence theorem and finite-index
restriction theorem have published proofs. The general restriction
injectivity needed here remains dependent on the central split-torus
character-detection theorem. Defining this target does not discharge that
obligation. The target is useful independently of a choice of splitting
coordinates because its conclusion only refers to intrinsic positive
points and the actual map `i`.

This module does not identify that positive image with the neutral
component of the real points of the greatest rational split centre after
Weil restriction from `F` to `ℚ`. That comparison is required separately
to identify the source's particular `A_G` with this construction.
No rational-quotient comparison, Haar normalization, unimodularity,
finite volume or Siegel coverage is asserted here.
