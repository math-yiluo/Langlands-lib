# Quotients from a supplied intrinsic isotypic range

`Langlands.quotientOfIsotypicRange` constructs an actual surjective intertwiner
from a representation `rho` to an irreducible representation `sigma`. The
field, monoid, ambient carrier and irreducible carrier have four independent
universes. No topology, smoothness, admissibility or finite length is used.

The inputs include an actual endomorphism `P` of `rho`, its range equality
with the supremum of all ranges of intertwiners from `sigma` to `rho`, and the
assertion that no subrepresentation of `P.ker` surjects onto `sigma`. There is
also an actual occurrence of `sigma` as a subquotient of `rho`, expressed by
a subrepresentation and a surjective intertwiner. The output is a subtype
containing a quotient map and its surjectivity proof. Existence of `P` remains
an explicit premise of this constructor. Idempotence is unnecessary for this
algebraic step.

The implemented proof first shows that `P` is nonzero. If it were zero, the
given subquotient would lift to the entire kernel, contradicting the kernel
condition. Hence the intrinsic isotypic sum is nonzero, and some intertwiner
from `sigma` to `rho` is nonzero. Irreducibility makes this map injective.
The intrinsic sum is semisimple as a sum of images of a simple module. Restrict
the injection to `P.range`, split it there, and compose the retraction with the
surjection of `rho` onto `P.range`. Classical choice packages this construction
as an actual quotient map.

This is internal derived algebra, motivated by the scalar-central-character
step of the discrete-series opposite Jacquet quotient argument. It does not
assert a new analytic fact and is not a verbatim theorem from the literature.
The generic image and supremum lemmas are imported from
`CompactCoefficient.IsotypicSemisimplicityProof`; their hypotheses are purely
algebraic and contain no compact-coefficient assumption. The actual
`semisimpleRetraction` construction is imported from
`Classification.OppositeJacquetReciprocity`. Neither imported result assumes
the discrete-series Jacquet quotient criterion. This constructor supplies no
analytic projector, central-character reduction or Jacquet calculation.
