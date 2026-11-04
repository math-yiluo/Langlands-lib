# Semisimple replacement and centralizer spanning over arbitrary fields

This derived module applies the actual translation Jordan construction over
perfect fields to tangent centralizers, and combines it with the published
positive-characteristic prime-power construction. The final spanning theorem
retains the explicit geometric noncentral semisimple premise, the finite
coordinate datum, affineness and local finite type. It applies to every infinite
ground field, including imperfect fields in positive characteristic, and every
same-universe field extension. Cartan generation is not asserted.

The finite linear algebra helpers identify the canonical semisimple component
of zero by uniqueness, and show that the canonical semisimple component of an
endomorphism kills every vector killed by that endomorphism. For the latter,
the map from the ground field sending a scalar to its multiple of the vector
intertwines zero with the original endomorphism. Jordan naturality evaluated at
one gives the claim.

The actual adjoint differential sends `semisimpleKernel` to its canonical
semisimple component by applying `tangentMatrix_semisimpleKernel` to the actual
adjoint representation. The tangent centralizer is the kernel of its own adjoint
differential, so the preceding zero-vector lemma gives centralizer inclusion.
Every vector lies in its own centralizer and therefore in its semisimple
component's centralizer. If the latter were the whole tangent module, its adjoint
differential would vanish. The original adjoint differential would then equal
its nilpotent Jordan component. Consequently a nonnilpotent adjoint differential
forces the constructed semisimple component's tangent centralizer to be proper.
Its representation-tested geometric semisimplicity was already proved in the
translation construction.

For any field, characteristic zero implies perfection and supplies the Jordan
replacement. In prime characteristic the existing simultaneous prime-power
replacement supplies the same noncentral semisimple covering. These cases cover
all fields. `noncentralSemisimpleReplacement` chooses one such actual element
on the nonnilpotent adjoint locus, and its properties theorem records geometric
semisimplicity, properness and membership. Over an infinite field the existing polynomial nonnilpotent-locus
theorem, under the explicit geometric premise, gives a nonempty spanning locus
of nonnilpotent actual adjoint differentials. Every vector in that locus lies
in one of the noncentral semisimple centralizers. Their supremum thus contains
a spanning set and is the whole actual Lie module, and the nonempty locus gives
a ground-field noncentral semisimple element.

All content is internal and derived from the imported actual adjoint, Jordan,
prime-power and polynomial-locus results and Mathlib's characteristic dichotomy.
No smoothness or connectedness premise is introduced. No noncentral geometric
semisimple element or Cartan subgroup is constructed from group structure here.
