# Combining linear vector coordinates and the characteristic-zero case

This internal construction supports the existing split-torus vector-linearization
target at arbitrary universe `u`. It is derived from the Library's all-test
vector-coordinate definitions, actual product point equivalence, isomorphism
transport, and characteristic-zero scalar-linearity proof. It proves the
coordinate-combination step and the characteristic-zero existence case. The
positive-characteristic existence of a fixed/moving product decomposition remains
a separate proof obligation.

`vectorTupleProductEquiv` concatenates two finite tuples and restricts to the
first and second coordinate blocks to invert concatenation. Addition is preserved
coordinate by coordinate. Both block lengths may be zero.

`vectorProductCoordinates` composes the actual product point equivalence with the
two supplied coordinate equivalences and tuple concatenation. Its two evaluation
formulas identify the blocks with the actual product projections.
`IsNaturalVectorCoordinates.prod` uses these formulas and naturality on each
factor to prove naturality under every test morphism.

The two scalar-projection formulas apply the coordinate equivalence to its
inverse and read off a coordinate block. They show that scalar multiplication in
concatenated coordinates projects to the supplied scalar multiplication in each
factor. `IsLinearVectorCoordinates.prod` uses these formulas, scalar linearity on
each factor, and the two explicit hypotheses that the actual product action
intertwines the factor actions under the actual projections. No product action
or equivariance law is assumed implicitly.

`IsNaturalVectorCoordinates.isLinear_of_act_eq` proves scalar linearity in any
natural vector coordinates for an actual action fixing every point on every
test. This is the elementary coordinate step for a fixed vector factor; it does
not construct that factor or its coordinates.

`IsNaturalVectorCoordinates.of_iso` transports natural coordinates through an
actual group-scheme isomorphism, using the Library's `vectorCoordinatesOfIso`.
`IsLinearVectorCoordinates.of_iso` additionally assumes that the inverse
isomorphism intertwines the two actual actions. Applying the transported
coordinate equivalence to its inverse identifies scalar multiplication after
transport. This identity and equivariance reduce scalar compatibility to the
original linear-coordinate hypothesis.

`IsVectorGroup.exists_linearCoordinates_of_charZero` takes a vector-coordinate
witness from the actual vector-group predicate and applies the published
`isLinearVectorCoordinates_of_charZero` theorem. The acting group must be affine;
the field need not be algebraically closed. The split-torus specialization
obtains affineness from `IsSplitTorus.isAffineHom`. These results allow dimension
zero and retain all tests, including nonreduced, nonaffine and empty tests.

The characteristic-zero source comparison is documented in
[SplitTorusVectorLinearizationStatement.md](SplitTorusVectorLinearizationStatement.md):
Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015), A.1.1.
[VectorActionCharZero.md](VectorActionCharZero.md) documents the internal proof.
This contribution's provenance is internal: its proofs use
the named, already proved Library inputs and elementary coordinate identities,
without invoking an additional original-source theorem.
