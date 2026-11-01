# Openness of actual corrected Bruhat supports

This internal proof supplies the topology needed for corrected support quotients.
A Weyl support is length compatible if it contains every permutation strictly
longer than any of its members; elements of equal length may be chosen in any
order. The actual matrix Bruhat union of such a support is open. The proof takes
the finite union of excluded cells and uses the published strict inversion
decrease on each cell boundary to prove this excluded union closed.

The elementary `inversionLength` is identified with the published boundary
count. The inverse-permutation convention in `borelCell` is related explicitly
to the published upper Bruhat cell; inversion preserves this count.

The main topology argument is the compact-representative criterion for a
two-sided support core. If each left subgroup element is a Borel factor followed
by a member of a compact set, and each right subgroup element is a compact
representative followed by a Borel factor, then membership in the core of a
Borel invariant open set can be tested over a compact product of representatives.
The set of failures is closed in the product. Its projection is closed because
the parameter space is compact. Its complement is the desired open core.

For the supplied p-adic field and topology, Iwasawa decomposition gives these
compact representatives inside each standard parabolic: intersect the compact
integral group with the closed parabolic. If a parabolic matrix becomes upper
triangular after multiplication by an integral matrix, that integral matrix
also belongs to the parabolic. This proves the left factorization; inversion
gives the right factorization. This reasoning includes rank zero.

`isOpen_corrected_bruhatSupport` combines this compact argument with the actual
matrix two-sided-core identity. Consequently every length-compatible Weyl tail
has open corrected matrix support for every source and target block shape.
Finally the actual inducing quotient support is open, by the quotient topology
and the proved exact preimage identity.

The provenance is internal. The module uses the published Bruhat boundary,
Iwasawa, compact integral group and corrected matrix support results. It supplies
no geometric coefficient identification, graded cut-map comparison or exactness
conclusion.
