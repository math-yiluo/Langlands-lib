# Admissibility of the actual normalized opposite Jacquet quotients

Author: Worker 166.

`Langlands.Parabolic.normalizedOppositeJacquetAdmissibility` proves the exact
published `NormalizedOppositeJacquetAdmissibilityStatement.{uF,uV}`. It
assembles all five clauses: standard, refined, composed, flattened refined,
and flattened composed. The field and representation-carrier universes are
independent. Every natural rank, including zero, every ordered block shape
and refinement, and every admissible complex input representation are
retained. The carrier itself need not be finite dimensional.

## Arbitrary product-Levi input

The main new argument is `isAdmissible_refinedOppositeJacquetAction`.
Smoothness of the actual quotient action follows from the published smoothness
theorem. To prove finite dimensionality of the fixed space for an arbitrary
open subgroup `L` of the refined Levi, use its subtype topology to obtain an
identity neighbourhood `U` of the ambient product Levi whose intersection
with the refined Levi lies in `L`. The published product neighbourhood basis
supplies compact open subgroups `K i`, each admitting the inner block Iwahori
factorization, whose product `KP` lies in `U`. Thus the subgroup `J` obtained
by pulling `KP` back to the refined Levi lies in `L`.

Choose a strictly contracting upper scalar tuple in each component using
`deepChamberNonempty`. The inverse tuple is the scalar used for the opposite
canonical-lift map. Admissibility of the original representation makes its
`KP`-fixed space finite dimensional. The actual all-power stable image is a
submodule of this space. The published
`Jacquet.refinedOppositeStableImageJacquetBijective` makes its map to the
`J`-fixed opposite quotient surjective, so that target fixed space is finite
dimensional. Inclusion of the `L`-fixed space into the `J`-fixed space gives
the required finite dimensionality for `L`.

Here `σ` is the direct `Jacquet.action` on the refined Levi. Its action is
definitionally the same as `refinedOppositeJacquetAction`, which is written
as a pullback from the radical normalizer. The proof's inclusion therefore
compares the actual fixed spaces without an assumed compatibility map.
No restriction to an individual factor is assumed admissible, and no tensor
decomposition or finite length hypothesis is used. Empty products are covered
by the same product neighbourhood and component-choice constructions.

`isAdmissible_normalizedRefinedOppositeJacquet` then applies the published
open-kernel twist theorem. The character is precisely the inverse half of
`refinedOppositeLeviModulus`, the inverse of the full upper modulus. Its
kernel is open by the existing theorem, so this twist is the required positive
upper half-modulus normalization of the actual lower-radical quotient.

## Composed quotients and flattened coordinates

For the composed quotient, first apply the published
`isAdmissible_standardOppositeJacquet` to the original GL representation,
then the new refined result to that actual outer opposite quotient.
`normalizedOppositeRefinementTransitivity` supplies the equivariant linear
equivalence from this iterated normalized quotient to the direct composed
normalized quotient. Admissibility transports through that equivalence by
`isAdmissible_of_equiv`. In particular the composed action retains both the
outer and inner normalizing characters.

The two flattened clauses apply `isAdmissible_comp_continuousMulEquiv` to
`flattenedLeviEquivContinuous`. Its underlying homomorphism is exactly the
`flattenedLeviEquiv` used in the target statements. The supplied field topology
and its compatible module topology provide the topological ring instance
needed for this continuous equivalence. Each closed clause is then packaged
with its unchanged quantifiers, and the final theorem forms the conjunction
with the already proved standard clause.

## Provenance and boundary

This is an internal deduction from the published product opposite canonical
lifts, product compact-open neighbourhood basis, open-kernel twist invariance,
standard opposite admissibility, normalized opposite transitivity, and
admissibility transport theorems. The product fixed-space argument is the
analogue of `StandardOppositeJacquetAdmissibilityProof`, applied directly to
the product group and its actual refined subgroup. The transitivity proof is
imported from Worker 430's published module; no draft is copied here.

The original mathematical motivation is Casselman's Chapter III, revision
April 29, 2019, especially Proposition III.5.5 and Theorem III.5.6 on page 7,
as cited and scoped in `OppositeJacquetAdmissibilityStatement.md`. The present
implementation uses its already proved canonical-lift prerequisite and the
finite-dimensional fixed-space consequence over complex coefficients. It
does not extend the source's claim to arbitrary Noetherian coefficient rings.

This proves the complete opposite-admissibility prerequisite. Second
adjointness, multiplicity comparisons, and the generic constituent comparison
with its irreducible-head consequence remain separate obligations.
