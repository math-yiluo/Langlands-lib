# Prescribed-level congruence generation by integral root intersections

This module is internal derived content. It combines the published local
root-product isomorphisms, ordered-product point formulas and dynamic
integral three-factor cell. It concerns actual section restriction kernels;
comparison with positive-depth Bruhat–Tits root fixers remains a separate
obligation.

`range_inf_restrictionKernel_le_of_orderedProductIso` works over any base
scheme and any morphism of bases. Its data are an ordered finite product of
group schemes, an isomorphism from that product to a group scheme U, a
monomorphism from U to the ambient group, and the equation identifying the
composite with the original ordered multiplication. A subgroup of ambient
sections that contains the intersection of each factor image with the
restriction kernel contains that intersection for U as well. The product
multiplication is monic. Cancelling it shows that a product section that
restricts to the identity has every coordinate restricting to the identity.
The ordered point formula and closure of the subgroup under finite products
then give the assertion. The finite product may have no factors.

`dynamicUnipotent_inf_restrictionKernel_le_of_exponentRoots` specializes this
to a smooth affine group with geometrically connected fibres over a local
domain R, equipped with a map from a coordinate split torus. One field
R-algebra k is supplied, and the induced torus map on that fibre is monic
and has a relative root system. For any exponent cocharacter and any base
restriction, containing the restriction-kernel intersections of the
integral root functors whose characters are roots on this fibre implies
containing the corresponding intersection of the dynamic unipotent.
The proof enumerates the indivisible positive roots, chooses the smooth
integral root representatives, proves disjointness of their positive rays
from the root system, and uses
`exists_orderedRootProductIso_localRing` and the preceding cancellation
lemma. All the root functors are the actual integral functors for the
original torus map.

`congruenceKernelAt_le_of_exponentRoots_and_dynamicCentralizer` takes an
integral model M over a local domain R with fraction field K, smooth group
scheme with geometrically connected fibres, and a coordinate split torus
map whose induced generic-fibre map is monic and has a relative root
system. At every specified positive integer n, a subgroup Q of the original
integral section group contains `M.congruenceKernelAt n` if it contains
both the intersections of this kernel with every integral root functor
selected by the generic roots and its intersection with the dynamic
centralizer of the chosen exponent cocharacter.

The last proof uses `DynamicModels.tripleCell M` and its
`congruenceProductEquiv n`: every original congruence section is an ordered
product of congruence sections in the opposite unipotent, centralizer and
unipotent models. Their model maps preserve the prescribed congruence
level. The second theorem puts both unipotent factors in Q, and the
centralizer premise puts the middle factor there. The point formula for
the product equivalence retains the original section and proves its
membership in Q.

`exponentRootCentralizerCongruenceSubgroup M I i ν n` defines the join of
these actual integral root intersections with the dynamic-centralizer
intersection. `exponentRootCentralizerCongruenceSubgroup_eq` identifies this
explicit generated subgroup with `M.congruenceKernelAt n` under the same
generic root-system and smooth connected model hypotheses. One inclusion
uses that every generator lies in the original kernel; the converse is the
preceding containment theorem applied to this defined subgroup.

No Henselian or separably closed residue-field hypothesis is used. These
results assert neither existence of an integral model nor identification
of a congruence root intersection with a strict-depth building root fixer.
They do not yet bound the full radical reduction preimage or prove the host
opposite-factor statement.
