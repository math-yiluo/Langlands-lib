# Filtered collection for roots selected by a character semigroup

This is an internal prerequisite for the actual building comparison. It derives
filtered products from an existing valuation; it does not assert existence of an
initial valuation, apartment, or building.

Let `k` be a field in any universe, let `G` be a smooth affine group scheme over
`k`, and let `i : T.toGrp ⟶ G` be a monomorphic split-torus homomorphism. Retain
`IsSplitTorus T.toGrp`, `HasOppositeFactorPairs i`, and an existing family `φ`
with `hφ : IsRootDatumValuation i φ`. Let `A` be an additive subsemigroup of the
actual character lattice of `T`. Write

`Ψ = {a | a ∈ relativeRoots i ∧ a ∈ A}`.

For collection, a supplied cocharacter `ν` has strictly positive integral
pairing with every element of `Ψ`. The depth function
`f : characterLattice T →+ ℝ` is additive. Its values may be negative.

## Constructions and conclusions

`selectedRootDepthSubgroup hφ A f` is the supremum, inside the original group
`rationalPoints G`, of `hφ.filtrationSubgroup a (f a)` over every `a ∈ Ψ`.
Each factor is the actual filtration
`{g ∈ rootGroupPoints i a | (f a : WithTop ℝ) ≤ φ a g}`.
`selectedRootDepthSubgroup_eq_closure` identifies this supremum with the subgroup
closure of the union of those actual sets. These definitions use the existing
valuation and do not assume a product decomposition.

`exists_semigroupIndivisibleRoot_eq_or_double` proves that each element of `Ψ`
is a root indivisible among the selected actual roots, or twice one. The
indivisibility here is exactly `RelativeRoot.semigroupIndivisibleRoots i A`;
it is neither global root indivisibility nor primitivity in the character
lattice. This lemma uses smoothness, splitness, the monomorphic torus map and
the original opposite factor pairs. It does not use an affine root system or
an apartment.

`orderedRootFiltrationProduct_eq_selectedRootDepthSubgroup` says that every
finite enumeration `a : Fin n → characterLattice T` of exactly those selected
indivisible roots has the prescribed ordered product at depths `f (a j)` equal
to `selectedRootDepthSubgroup hφ A f`. The conclusion is an equality of actual
sets of original rational points. In particular, the ordered product has the
subgroup structure supplied by the displayed supremum. This equality allows
repetitions and the empty enumeration. `orderedSelectedRootFiltrationProduct_order_independent`
compares any two such enumerations, including different lengths.

`selectedRootDepthSubgroup_le_semigroupSubgroup` places the filtered subgroup
inside the existing actual subgroup selected by `A`, on the field test scheme.
It needs splitness and the existing valuation, with smoothness and the
monomorphic torus map retained; it does not need opposite factor pairs,
positivity, or a product premise.

When `0 ∉ A` and the enumeration is injective,
`mem_selectedRootDepthSubgroup_iff_existsUnique` strengthens collection to
unique actual filtration coordinates. Every element of the generated subgroup
has exactly one tuple `x j ∈ rootFiltration i φ (a j) (f (a j))` whose product
in the supplied order is that element.

## Implemented proof and provenance

This is a source-free internal derivation from the existing Library:

- `isClosedPositiveRootDepth_of_addSubsemigroup` proves closure of `Ψ` under
  positive root combinations using positive-multiple closure and addition in
  `A`. Additivity of `f` makes the required depth inequality an equality.
- The existing `IsRootDatumValuation.filtrationSubgroup_double_le` from
  `PositiveDepthRayCompression` is applied with `s = 2*r` and `le_rfl`:
  the filtration of `2a` at `2r` lies in that of `a` at `r`, for every real
  depth. Its V4 proof handles finite valuation values and the top value.
- The existing selected-ray coverage theorem supplies a selected indivisible
  root below every selected root. The existing opposite-pair multiplier bound
  restricts its positive multiplier to one or two.
- The proof inserts adjacent pairs `a j, 2 • a j`; a nonroot second character
  contributes the bottom subgroup. `positiveDepth_commutator_height`, derived
  from V3, supplies a strictly increasing positive height for commutators of
  all actual factors. `HeightCollection.range_orderedProduct_eq_iSup` collects
  them in their supplied order. Coverage identifies the supremum with the
  subgroup defined above. The existing public pair-absorption theorem
  `range_orderedProduct_pairs` in `ChamberPositiveCollection`, together with V4,
  collapse each adjacent pair to its selected first factor.
- Inclusion in the ambient semigroup subgroup follows from the existing cyclic
  root/semigroup comparison and monotonicity. Unique coordinates then follow
  from `RelativeRoot.mem_semigroupSubgroup_iff_existsUnique_rootPointsProduct`
  on the field test scheme: filtration coordinates are also intrinsic root
  coordinates, so their ambient point values agree component by component.

All root functions and point subgroups are the original Library objects.
This module proves no smaller-torus normalizer or opposite valuation law,
initial valuation existence, geometric building axiom, or supplied-model
special point. The full `BuildingComparisonStatement` remains an obligation.
