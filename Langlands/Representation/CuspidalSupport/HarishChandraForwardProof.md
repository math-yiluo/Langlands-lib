# Forward Harish-Chandra compact-support proof

Authors: Worker 200, with Worker 237's gap-vanishing helpers and the compact
coset-cover argument adapted from his shared admissibility draft revision 3,
and Worker 252's unchanged dual-averaging helpers from shared HC draft revision 2.
These helper theorems take the Cartan proposition as an explicit hypothesis.
`HarishChandraAssembly` supplies the actual theorem
`Langlands.GeneralLinear.Cartan.cartanDecomposition` to prove the unconditional
Harish-Chandra equivalence.

`hasCompactSupport_average_determinantUnit_of_cartan` treats an arbitrary
smooth quasicuspidal representation and one vector. The integral product Levi
is compact and open, so the vector has a finite orbit under it. Finitely many
left translates modulo the averaging subgroup cover this compact group.
The gap-vanishing lemma supplies one bound for these finitely many translates
and vectors.

For a group element in the determinant-unit subgroup, a blockwise Cartan
factorization has zero sums of exponents. A nonzero averaged translate cannot
have a gap above the uniform bound. Only finitely many zero-sum bounded-gap
tuples remain. The support therefore lies in a finite union of compact double
cosets. The determinant-unit subgroup is closed, so the inverse image of this
compact union is compact. This proves compact support in the subgroup's actual
topology, with no condition on the representation's dimension or irreducibility.

`hasCompactSmoothDualCoefficients_of_isLeviQuasicuspidal_of_cartan` completes
the coefficient step. The boundary comparison transfers smoothness of a
functional for the restricted dual to smoothness for the ambient dual.
Worker 252's compact-open basis and dual-averaging lemma then give a compact
open subgroup over which averaging leaves this functional unchanged. The
matrix coefficient equals the functional composed with the averaged orbit.
Since a linear functional maps zero to zero, this composition has support
contained in the compact support already proved. No topology or continuity
on the representation space or on the functional is needed.

Both results cover every rank, including the empty product. The separate
boundary proof also provides the exact rank-zero equivalence.

This is derived proof infrastructure for Bernstein–Zelevinsky (1976),
literature id `bernstein-zelevinsky-1976-representations-gln`, Theorem 3.21 and
Lemma 3.22, pp.34–35. The finite coset cover makes the contraction bound uniform
in the two compact Cartan factors. The zero-sum restriction removes the
unbounded block-scalar directions in a general Cartan chamber. We use the
source's contraction and averaging ideas directly, without importing the
full averaged-orbit characterization in §2.40 as an extra premise.
