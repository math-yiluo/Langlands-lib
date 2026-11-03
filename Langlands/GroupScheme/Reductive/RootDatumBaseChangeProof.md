# Actual root data under arbitrary field extension

Worker 416. This internal proof unit proves the published
`SplitRootDatumFieldExtensionStatement` at arbitrary universe `u`.
The field extension is unrestricted.

`IsNormalizingPoint.exists_baseChange` regards a normalizing representative as
an inner conjugacy between the torus inclusion and its precomposition by the
torus automorphism. The published `HomConjugate.baseChange` transports this
conjugacy to the actual scheme pullback. Functoriality of composition identifies
its target with the inclusion precomposed by the pulled-back automorphism.
The result asserts existence of the representative needed by `IsRootDatumOf`.

`characterAut_baseChange` follows from compatibility of character pullback with
precomposition. In particular it uses the inverse of the torus automorphism,
as required by the published character action convention.

`IsRootDatumOf.baseChange` proves the three clauses of the actual root-datum
predicate. The pairing clause is the canonical lattice-pairing comparison.
The root-range clause uses the proved actual root-support comparison and the
image of a function's range under character pullback. For each reflection,
the old normalizing point supplies a representative after pullback. Surjectivity
of the canonical character-lattice equivalence reduces equality of the two
actions to an old character, where character-action naturality, the transported
reflection formula, and the old representative's action prove equality.
This helper works for any affine, locally finite-type field group and any split
torus homomorphism with a supplied actual root datum; it needs neither
reductivity nor maximality.

`splitRootDatumFieldExtension` specializes that helper to the published
statement. Connected reductivity supplies affineness and smoothness, hence
local finite type. The proof uses the actual spectrum map of the field's
algebra map and the actual group-scheme pullback functor throughout.
The stronger helper also allows the root index type an independent universe.

The provenance is an internal derivation from the published conjugacy,
character-lattice, Lie-weight, and root-datum transport interfaces. This unit
assumes a supplied root datum; it does not construct one or prove the host
simple-connectedness field-extension theorem.
