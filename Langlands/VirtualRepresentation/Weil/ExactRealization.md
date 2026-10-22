# Canonical irreducible-lattice realization in exact K0

Author: Worker 16.

This internal, derived construction connects the published irreducible lattice
in `Weil.Generic` to the actual exact-sequence quotient in
`VirtualRepresentation.Exact`. It uses their existing definitions and universal
linear extension; it introduces no additional representation-theoretic premise.
The group and representation-carrier universes are independent. An arbitrary
group topology suffices, with no topological-group hypothesis.

`ContinuousClasses G` is the genuine isomorphism quotient of all
finite-dimensional continuous complex representations. Continuity uses the
existing usual complex module topology. `ContinuousExactGroup G` is exactly
`ExactGrothendieckGroup (fun A => A.IsContinuous)`, whose relations come from
actual short exact sequences with continuous terms, including nonsemisimple
objects. Zero-dimensional objects remain allowed in this target.

`forgetIrreducibleClass` uses `Quotient.map` to discard only the irreducibility
proof from a continuous irreducible object. The same invertible intertwiner
witnesses its compatibility with both isomorphism relations. The subsequent
`basisContinuousClass` discards the positive rank label. The proved forgetful
comparison identifies its underlying representation class with Generic's
`underlyingClass`; the rank carried by the source basis consequently gives its
actual dimension. No representative of an arbitrary quotient is selected.

`realizeExact` is the integer-linear extension of
`ExactGrothendieckGroup.ofClass` on these continuous classes. Its generator,
actual irreducible object, zero, addition and integer-scalar evaluation laws are
proved. The actual-object law accepts explicit continuity, irreducibility and
positive-rank proofs and sends that generator to the object's own exact class.
The full target type imposes continuity only, not irreducibility or
semisimplicity.

`degree_comp_realizeExact` identifies the composite with the genuine exact
degree as the rank-weighted degree from Generic. Its proof checks the
single-coordinate generators and integer linearity, uses the already proved
exact quotient's degree evaluation, and then uses the rank equality retained
by the source basis. `degree_realizeExact` is the pointwise formula. The
exact-degree construction itself relies on the published rank-nullity proof
for short exact sequences; no splitting is needed here.

`ExactExpansion G x v` is the proposition `realizeExact G v = x` for a specified
finite irreducible combination `v`. The equality, generator, actual-object and
zero specifications are proved, as is expansion of each combination's own
image and degree compatibility of any asserted expansion. None of these
claims existence or uniqueness of an expansion for an arbitrary exact class.

The `LocalWeil` declarations specialize directly to the constructed
`Langlands.Weil.Local.localWeilGroup F` for every prime and actual p-adic field.
They reuse `LocalWeil.Lattice` and `Basis` definitionally and preserve the
independent field and carrier universes. The local map and expansion relation
are abbreviations of the generic ones; local generator, actual-object and
degree formulas are provided.

## Provenance and boundary

The imports are the published `Weil.Local` (which imports `Weil.Generic`) and
`VirtualRepresentation.Exact`. The underlying finite representation and
isomorphism quotient definitions come from `Weil.Representation.Basic` and
`Predicates`; integral extension comes from `VirtualRepresentation.Integral`.
The mathematical content here is the internal composition of these published
constructions. The paired source accounts of Generic/Integral and Exact give
their respective Henniart and Tate provenance; this file introduces no new
literature claim or independent literature theorem.

The existing `realizeVirtual` in `Weil.Realization` lands in the split
Grothendieck group. This module instead lands in the published quotient by actual short
exact-sequence relations, and neither imports nor changes that split
realization. It asserts no split-to-exact isomorphism, decomposition theorem,
Jordan–Hölder uniqueness, bijectivity, inverse or multiplicities on arbitrary
exact classes. Those substantive comparison results remain separate tasks.
No inertia-support comparison, break extrema, tensor decomposition,
determinant or epsilon system is included.

## Development validation

The module compiles with zero errors and warnings in Lean 4.34.0 with pinned
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Inspection of `realizeExact`
reports independent universe parameters `uG` and `uV`. Private complete-type
checks assign the unapplied constants to expanded signatures for the
forgetful map, realization, expansion relation, degree comparison and
actual-object law, and for the local realization, relation and degree law.
All pass with independent generic group/carrier and local field/carrier
universes. Inspection of the main map and axiom diagnostics for the degree
comparison, object law and local map report only `propext`, `Classical.choice`
and `Quot.sound`. Compilation is development evidence; independent semantic
review and Library publication remain separate requirements.
