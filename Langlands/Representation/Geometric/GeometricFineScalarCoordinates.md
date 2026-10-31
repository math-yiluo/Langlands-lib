# Fine scalar coordinates for a geometric intersection

This internal construction continues the actual inverse-conjugation
construction. It works over an independently universed commutative ring and
keeps the supplied actual source and target refined Levi equalities.

The imported dependency `IntersectionChamberCoordinates` is Worker 828's
published coordinate module. The extension defines no duplicate label
or tuple map. It uses `chamberIndex` and `chamberRestriction` from that unit.
They read the target block at the image of the first source fine coordinate and
pull a coarse tuple back along that label. Positive block sizes supply those
first coordinates; rank zero has an empty labeling.

`inverseRefinedIntersectionEquiv` exhibits the actual inverse
intersection homomorphism as an equivalence, using the same subgroup equality
identifications and inverse matrix conjugation. Its application agrees with
the preceding homomorphism by reflexivity.

`inverseCoarseScalarIntersectionHom_mem_center` first notes that
the target coarse scalar commutes with every target refined element, since
it already commutes with every element of the ambient target product Levi.
The constructed equivalence sends this central element to the center of the
source refined Levi.

The fine-scalar formula transports that central element through the actual
flattened Levi equivalence and uses the published `blockScalarToCenter`
bijection to write it as a tuple of fine scalars. The proved ambient
inverse-conjugation formula and the published permutation entry formula
identify the diagonal entry at the first coordinate of each fine block.
It is exactly the target scalar at the label defined above. Equality of units
then identifies the full tuple, proving that the actual inverse-conjugated
coarse scalar is the flattened block scalar of the explicit pulled-back tuple.

`inverseCoarseScalarIntersectionHom_eq_fineScalarHom` packages the pointwise formula as equality of the actual monoid homomorphisms.
`geometricPiece_coarse_character_reflects_fineScalars` rewrites the preceding actual geometric-piece reflection by this homomorphism equality. Its conclusion is occurrence on the actual normalized source refined Jacquet action, first restricted to flattened fine scalars and then pulled back along the explicit tuple map. This is the same restricted character; it is not an extension to the full source scalar torus.

The equivalence and scalar formulas hold over any commutative ring; they
require neither minimality nor whole-Levi conjugacy. The final character
reflection specializes to the supplied p-adic topological data and any smooth
source representation. It adds no admissibility, irreducibility, rank or
analytic hypothesis. These are internal consequences of the actual subgroup
and scalar constructions, with no new literature assertion. The module does
not extend a generalized character to the full fine center, identify a real
exponent, or prove filtration, branch exclusion, whole-induction isolation or
the parent Hom comparison. The provenance is internal: the implemented proof
uses the imported actual subgroup constructions, the public center/scalar
bijection and the permutation-matrix entry formula.

Worker 526 implemented the construction. Workers 359 and 430 supplied the coordinate, normalization and reflection design guidance during the parent Hom-comparison investigation.

Worker 828 authored the reused public chamber-coordinate dependency. The
generic reflection and central-evaluation APIs are also public imports.
