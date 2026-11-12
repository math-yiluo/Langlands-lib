# Existence of normalized actual common-closure reciprocity

`Langlands.LocalClassField.commonClosureReciprocityExistence` proves exactly
the published proposition `CommonClosureReciprocityExistence.{u}`. Its only
parameter is the carrier universe. In particular, the full statement
quantifies every prime, every p-adic field in that universe, and every
supplied base topological datum.

The implemented proof applies
`commonClosureReciprocityExistence_of_finiteGeometricCupComparison` to the
unconditional theorem `finiteGeometricCupArtinCharacterComparison`.
The latter identifies geometric inverse fundamental cup with the actual
finite carry symbol. Its proof reduces each Galois automorphism to the
cyclic subgroup it generates and transports the cyclic comparison along
the actual determinant-norm and cup/corestriction squares. The fixed
middle field need not be normal over the base.

The common-closure assembly uses the already constructed single family on
all actual finite intermediate fields of `AlgebraicClosure F.Carrier`.
Finite Galois restrictions separate the actual fixing-subgroup
abelianizations. The finite geometric comparison proves the remaining
transfer square for this family, and the established Galois-to-Weil
comparison gives the actual Weil transfer law. The assembly combines this
with the family's norm, conjugation, density, multiplicative completion,
and absolute-value normalization laws.

Consequently the witness consists of continuous group equivalences on
the quotients by closed commutators, with all six laws in
`NormalizedSystemRelation`. The extension-field data are exactly
`canonicalData F`; normalization uses `localResidueDegree F` over the base
and the supplied datum's residue cardinality. All finite intermediate
fields, including nonnormal ones, occur in the same family.

This is an internal composition of the imported proved comparison and
assembly theorems. It adds no family, comparison, reciprocity or
functoriality premise. The published target and its imported source pairs
are unchanged.
