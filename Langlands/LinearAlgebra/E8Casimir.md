# The Casimir identity for root data of type E₈

In `Langlands.LinearAlgebra.E8Casimir`, `Langlands.E8Casimir.IdentityStatement`
concerns a reduced integral root datum \(P\) with finitely many roots and
a base whose simple roots are numbered by `Fin 8`. Their Cartan pairings
are the entries of `CartanMatrix.E 8`. If the coroots span the
cocharacter lattice over \(\mathbb Z\), the sum over all roots satisfies

\[
  \sum_{\alpha}\langle x,\alpha^\vee\rangle\,\alpha=60x
\]

for every \(x\) in the character lattice.

`sum_toLinearMap_coroot_smul_root` proves the identity using the integral
simple-reflection rule from `Langlands.LinearAlgebra.RootReflectionCoefficients`.
The coefficient vectors are obtained by closing the eight coordinate
vectors under the simple reflections. Each nonnegative vector
is listed as a hexadecimal numeral, with the digit of vertex zero
at the right. The negative vectors are represented by the opposite
integers. Lean checks the finite certificate in the kernel. It verifies
that the codes are strictly ordered and recoverable from their vectors,
that all coordinate vectors occur, and that negation and each simple
reflection give the vector at the computed index. It also verifies that
each vector is a signed coordinate vector or is the simple reflection
of a vector with smaller absolute code.

By symmetry of the Cartan matrix, simple reflection acts by the same
rule on the coefficients of a root and the coefficients of its coroot.
Induction on the absolute code realizes each listed vector by such a
root and coroot. Conversely, induction on roots by simple reflections
and negation shows that every root occurs. Linear independence of
the simple roots and distinctness of the codes give a bijection with
the 240 indices.

Write \(c_a\) for the column of coefficients at index \(a\) and \(A\)
for the Cartan matrix. The kernel checks
\(\sum_a c_a c_a^{\mathsf T}A = 60I\) entry by entry. With the bijection,
this matrix calculation evaluates the root-coroot sum against each
simple coroot. The simple coroots span the cocharacter lattice by the
coroot span hypothesis, and the pairing is perfect. These facts give
the identity on the full character lattice.
