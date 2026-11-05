# Proof of pure-dimension locality and base change

This proof targets
`Langlands.AlgebraicGeometry.SchemeFiberGeometry.SchemePureDimensionComparisons.{u,v}`
from `SchemePureDimensionStatement`, via the theorem
`schemePureDimensionComparisons`. The full target retains arbitrary
locally finite-type schemes and morphisms, field extensions, actual
cartesian squares and residue-field fibres. It does not assert
constructibility or filtered descent.

For the open-cover assertion, first restrict pure dimension to any
actual open U. A component Z of U extends to the ambient component T
given by the closure of its image. Its restriction back to U is exactly
Z. The actual intersection homeomorphism identifies Z with the
nonempty open T ∩ U of T, so component open-dimension invariance
identifies its dimension with that of T. Conversely, choose a point
of any ambient component and a cover member containing it. Their
intersection is a component of that member. The same intersection
homeomorphism and nonempty-open dimension comparison identify its
dimension with that of the ambient component. The component invariance
was proved for all locally finite-type schemes over a field.

For scalar extension K/k, cover X by all its actual affine opens U and
cover the actual pullback P by their inverse images under P → X.
Both covers satisfy the locality equivalence just proved. Paste the
cartesian restriction square of each inverse image with the original
pullback square. Its canonical pullback isomorphism identifies that
inverse-image scheme with the scalar extension of U. Apply the affine
field-extension pure-dimension comparison and transport through this
actual isomorphism. The equivalence for every chart and the two locality
results give preservation and reflection for X. This argument includes
empty charts and imposes no quasi-compactness or separation assumption.

For a cartesian square of schemes, the actual fibre base-change
isomorphism identifies the new fibre at y with the scalar extension of
the original fibre at g(y) along the actual residue-field map. The
original fibre's structure morphism is locally of finite type because
it is a base change of the given morphism f. Apply the general
field-extension theorem to obtain the pointwise comparison, without an
affineness hypothesis on f or either fibre.

Apply this comparison at every y for preservation of the all-fibres
condition. For reflection along a surjective base map, choose a
preimage of each original target point and apply the same comparison.
The final theorem is the exact grouped target, with independent
scheme and cover-index universes. All empty fibres are included through
the vacuous componentwise condition.

The proof imports the published `AffineSchemePureDimensionProof` by
Lean name; that module imports the published `FiniteTypePureDimensionProof`.
Worker 105 authored the reused general scheme proof draft and these
predecessor proofs. The source provenance is the derived locality and base-change prerequisite for
Conrad Theorem 3.4(2), printed pp. 5–6, as documented in the unchanged
statement pair. This proves neither constructibility nor eventual
filtered descent.
