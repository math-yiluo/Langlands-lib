# Injectivity from an open cell of a group scheme

This is derived group scheme infrastructure for the cell comparison in Milne,
*Algebraic Groups* (2017), the last paragraph of 23.18. It proves triviality of
the full scheme-theoretic kernel, including on nonreduced tests.

Let D be a smooth geometrically irreducible group scheme over S. Suppose an
open immersion j : C → D contains the identity section, and the composite of
j with a homomorphism p : D → G is a monomorphism. Then `kernelι_eq_zero`
proves that the full kernel inclusion is zero, and `mono` proves that the
underlying scheme morphism of p is a monomorphism.

The implemented proof works over the full kernel K. In D × K it intersects
the inverse images of C under projection and the right kernel action. Both
opens meet every fiber over K: the identity and inverse of the universal
kernel point give sections into the respective opens. The fibers are
geometrically irreducible, so the intersection still covers K. The projection
from that intersection is smooth and surjective, hence an effective
epimorphism. Injectivity of p on C identifies the two D-valued maps there;
group cancellation and descent force the universal K-point to be the
identity. No smoothness or reducedness of K is assumed.

`surjective_intersection` supplies the fiberwise topological step. The helper
`lift` factors morphisms through an open immersion, and `eq_of_comp_eq`
applies injectivity on the cell to all test schemes. The result supplies only
this criterion; it does not construct the graph subgroup or prove the split
reductive isomorphism theorem.

If p is additionally flat, surjective and quasi-compact, `iso` constructs an
actual isomorphism D ≅ G with forward map p (`iso_hom`). It applies Mathlib's
`Flat.isIso_of_surjective_of_mono` and reflects the underlying scheme
isomorphism through the forgetful functors from schemes over S, monoid
objects and group objects. The quasi-compact hypothesis belongs to this
isomorphism construction, not to the kernel or monomorphism criteria.
