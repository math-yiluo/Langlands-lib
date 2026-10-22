# A common irreducible subquotient from a nonzero map

This internal algebraic proof targets `Langlands.NonzeroHomCommonSubquotientTheorem`
with independent coefficient, group, source-carrier and target-carrier universes.

The proof views the nonzero intertwiner as a map of group-algebra modules.
Artinianness makes the submodule lattice atomic, so its nonzero image contains
an atom N, which is a simple module. The inverse image of N in the source and N
in the target give actual subrepresentations. The restricted map is surjective;
the first isomorphism theorem identifies its kernel quotient with N. A second
use of the same theorem presents N as its identity-kernel quotient in the
target. Their composite gives the required equivariant equivalence of the two
actual subquotients. An explicit identity-on-vectors group-algebra linear map
transfers simplicity of N to the restricted target representation and then
through the first quotient equivalence to the source subquotient.

This uses only algebraic module facts from Mathlib and the published smooth
subquotient constructions. It requires no analytic induction results and no
finite dimensionality or finiteness condition on the source representation.
