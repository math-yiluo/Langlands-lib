# Ordered root products and full unipotent kernels

This derived internal construction uses the published ordered root-product chart
for split connected reductive groups over an arbitrary field. A supplied reduced
root datum on the actual torus character and cocharacter lattices gives reduced
rays: positive proportional roots are equal, and their positive integral
multiplicities agree. The proof uses reducedness and the torsion-free split
character lattice. `positiveRootEnumeration` chooses a finite ordering of exactly
the roots positive on a supplied integral cocharacter; this ordering carries no
additional geometric information.

Suppose both source and target are connected reductive over a field, with
specified split maximal tori and supplied reduced root data. Assume a bijection
between their root indices and an exact character pullback equation for a
supplied torus homomorphism. Also supply maps from the additive group that
represent every source root subgroup, and assume their composites with the
ambient homomorphism represent the corresponding target root subgroups. Under
these explicit hypotheses, `unipotent_kernel_trivial_of_root_correspondence`
proves triviality of the ambient map's kernel on the dynamic unipotent subgroup
of any source cocharacter.

The exact pullback equation identifies positivity in the source with positivity
on the pushed-forward target cocharacter. Enumerate the positive source roots,
then use the same order for corresponding target roots. Source ordered-product
surjectivity expresses a unipotent point in root coordinates. Postcomposition
with the ambient homomorphism commutes with this ordered product. If the point
is killed, injectivity of the target ordered-product chart makes every
coordinate zero. The source point is therefore the identity. The zero-product
and postcomposition identities also hold over arbitrary commutative rings.

All point statements quantify over every test scheme. The argument retains
infinitesimal points and does not assume a smooth or reduced kernel. It does not
construct root parametrizations, derive their image properties from an isogeny,
or supply the root-index bijection. It is an intermediate result toward the
centrality comparison in the general split reductive isogeny theorem.

The zero-coordinate identity `LocalSplitCell.orderedProduct_zero` is shared from `LocalSplitFieldComparison`; its statement and public name are unchanged.
