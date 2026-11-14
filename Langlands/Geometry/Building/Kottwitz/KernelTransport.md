# Group-theoretic kernel transport

These are internal algebraic helpers for the proof of Kaletha–Prasad,
*Bruhat–Tits theory: a new approach* (2023), Proposition 11.5.4, printed
page 431, PDF page 462. They assert only elementary facts about group
homomorphisms and do not establish any geometric premise of that proposition.

`map_kernel_eq_of_kernel_lift` considers a commuting square of group
homomorphisms. Assume that the map on points is surjective and that every element
in the kernel of the map on targets is the image of an element in the kernel
of the point map. To lift an element of the lower kernel, choose any lift on
points. Its upper image lies in the target-map kernel. Choose a correction in
the point-map kernel with the same upper image and divide by that correction.
The corrected lift belongs to the upper kernel. The reverse inclusion follows
directly from commutativity. In the intended application the correction input
is supplied by KP Proposition 11.5.3.

`comap_eq_of_map_eq_of_kernel_le` shows that a subgroup containing the kernel
of a homomorphism is the inverse image of its image. If a point has the same
image as a member of the subgroup, their quotient lies in the kernel, hence
the original point also belongs to the subgroup. This is the group-theoretic
step in the simply connected derived cocenter argument.
