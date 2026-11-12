# Transferring centrally normalized heights to original torus roots

This derived unit constructs the torus-coordinate adjustment needed after
central normalization of a parabolic factor. It uses actual adelic points,
actual group-scheme homomorphisms, intrinsic norm-one membership and normalized
idele norms throughout. It does not prove an arithmetic height bound, construct
a parabolic factorization, or conclude chamber reduction.

`PositiveRealTorus.centralAdjustedTorusPoint` sends an adjusting point `a` and
an original torus point `s` to `f(a)` inverse times `s`, using the actual adelic
map of the torus morphism `f`. The definition does not require positive points,
splitness or centrality. If a torus character is trivial on `f`, its normalized
idele norm is identical on the original and adjusted points. The actual
central split-torus root-restriction theorem supplies this triviality for every
actual relative root when the composite of `f` with the ambient torus inclusion
is central.

Suppose the raw ordered product is a unipotent image times a Levi image times
the original torus image, and it is also the central image of `a` times `p`.
Centrality lets the adjusting image commute past the first two factors.
Cancellation therefore expresses `p` as those same first two factors followed
by the adjusted torus image. This preserves their order.

If `p` is intrinsically norm one in the ambient group, the supplied Levi point
is intrinsically norm one in its own source, and the unipotent source is
unipotent, then the adjusted torus image is intrinsically norm one in the same
ambient group as `p`. The proof uses triviality of every ambient character on
the unipotent image, functoriality of norm-one membership for the Levi image,
and subgroup cancellation. It never infers intrinsic Levi norm-one membership
from membership in a larger group's norm kernel. Under all-test preservation
of the selected line on the three factors, the published height identity
identifies the adjusted torus height exactly with the height of `p`.

The final theorem allows a different adjustment for every point in an original
torus family. Assume each adjusted point maps into the intrinsic ambient norm
kernel, preserves the chosen root's normalized norm, and has selected-vector
height bounded by one fixed positive real constant. An actual positive integral
relation between the line character and that root gives a uniform bound on the
original family's root norms. The proof forms the family of all intrinsic
norm-one torus images with the specified height bound, applies the published
line-height and root-character comparisons to that family, and transfers the
bound using equality of root norms. The constant is chosen before all original
family points.

The construction and proofs are internal consequences of published central-root
restriction, unipotent character triviality, norm-one functoriality and exact
height identities. In a root-Levi application, the ambient group of this module
is that root Levi itself; identifying its canonical minimal-parabolic factors
with factors in the original group is a separate obligation.
