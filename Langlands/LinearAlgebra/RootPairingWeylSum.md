# Weyl sums on the span of roots

This is a derived linear-algebra construction using Mathlib's finite root
pairings, their natural Weyl action, and nondegeneracy on the root span.
It introduces no new result from the literature.

Let `P` be a crystallographic root pairing over a field of characteristic zero
with a finite root index type. A vector in the span of the roots fixed by all
root reflections is zero. Consequently the same holds for a vector in that
span fixed by the entire Weyl group. The statements apply to root pairings:
they do not require the roots to span the whole weight space.

The implemented proof uses the reflection formula to show that every coroot
pairs to zero with a reflection-fixed vector. Thus the vector belongs to the
kernel of the canonical root form. Mathlib proves that this kernel is disjoint
from the span of the roots for an anisotropic finite root pairing. Its
characteristic-zero crystallographic instance supplies anisotropy here.
Disjointness then forces the vector to be zero.

For a supplied finite enumeration of the Weyl group, `weylSum P` is the linear
endomorphism that sums the natural action of every Weyl element, without
division by the group order. Its value is fixed by every Weyl element, since
left multiplication permutes the summands. The Weyl action preserves the root
span because it permutes the roots. Therefore `weylSum P` vanishes on that
entire span.

The construction is general in all four type universes. It is an algebraic
ingredient for the averaging argument in the host task. It does not construct
the root pairing of an algebraic group, compare a central torus with a root
annihilator, or prove unipotent-weight positivity or a centralizer equality.
