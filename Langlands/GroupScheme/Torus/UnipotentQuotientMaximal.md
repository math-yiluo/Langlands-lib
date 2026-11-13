# Maximal tori through smooth connected unipotent quotients

This internal composition proves
`PerfectFieldUnipotentQuotientMaximalTorusStatement.{u}` over every perfect
field in universe `u`, in both characteristics. The source and target groups
are affine and locally of finite type. A closed inclusion `n : N ⟶ G`
represents the full kernel of an fppf quotient `q : G ⟶ Q`, expressed by
`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) q`. The kernel group
`N` is smooth, connected and unipotent.

If `i : T ⟶ G` is a maximal torus, then the actual composite `i ≫ q` is a
maximal torus of `Q`, with the same source `T`. Maximality is the existing
`IsMaximalTorus` predicate: the source is a torus, its map is a closed subgroup
inclusion, and any factorization through another closed torus has an
invertible source map. Thus the conclusion includes closedness and
injectivity as a morphism of schemes, as well as full maximality.
It does not merely assert maximality among split tori or among rational
points. The source torus need not split over the original field.

## Implemented proof

`IsMaximalTorus.comp_of_split_unipotent_kernel` first proves the result over
an arbitrary field when `N` is additionally split unipotent. Affineness of
`N` follows from its closed inclusion into affine `G`; smoothness supplies
local finite type. The published theorem `unipotentClosedSubgroup`
discharges the sole structural premise of
`IsUnipotent.closed_torus_quotient`, so the composite `i ≫ q` is closed.

The general published theorem `IsMaximalTorus.comp_of_torus_lifts` reduces
full maximality to two further properties, both proved here from published
inputs:

- `IsTorus.exists_splitUnipotentQuotientLift` lifts each closed target
  torus homomorphically through the specified quotient. Its structural
  premises are discharged by
  `RelativeRoot.splitUnipotentStableVectorSubgroup` and
  `RelativeRoot.torusVectorActionLinearization`.
- `subgroupConjugate_of_isTorus_fppf_split_unipotent_kernel_of_structuralStatements`
  compares every two homomorphisms from the same source torus that become
  equal after `q`. Its three structural premises are discharged by those
  same two theorems and `splitUnipotentAffineTorsorStatement`.

For a proposed larger target torus, the general theorem lifts it, compares
the induced source map with `i` by rational conjugation, and applies the
original full maximality to make the factor map invertible. No quotient
maximality, torus-lifting property, conjugacy property or homomorphic section
is retained as an extra premise of the new theorem.

`IsMaximalTorus.comp_of_perfect_field_unipotent_kernel` applies
`perfectFieldUnipotentSplit` to the actual smooth connected affine kernel,
then invokes the split-kernel result. Introducing the displayed universal
binders proves `perfectFieldUnipotentQuotientMaximalTorus`.

## Provenance and scope

The argument is an internal composition of the named published Library
results in `Torus/QuotientMaximal`, `Torus/UnipotentQuotientClosed`,
`Rational/SplitUnipotentQuotientTorusLift`,
`Rational/TorusUnipotentLiftConjugacy`,
`Rational/SplitUnipotentStableVectorProof`,
`Rational/TorusVectorLinearizationProof`,
`UnipotentClosedSubgroupProof` and `Unipotent/PerfectFieldSplitProof`.
It introduces no new literature assertion, mathematical axiom, group
predicate or quotient construction.

The smooth model, quotient homomorphism and its full-kernel identification
are supplied. This result does not construct parahoric models, geometric
special-fibre maps, facet/parabolic correspondences, residue-torus lifts to
integral models or prescribed-point special apartments. It therefore does
not prove `UnramifiedFixedPointSplitTorusStatement`.
