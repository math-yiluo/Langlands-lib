# Inverse transpose and the dual of reversed normalized induction

`Langlands.AllFieldBZ.Parabolic.ProductDualReversalStatement` concerns
an ordered block shape \(B\) and a family of irreducible smooth complex
representations \(A_i\) of its block groups over a nonarchimedean local
field. Let \(I_B(A)\) be their normalized induction from the standard
upper block parabolic, and let \(\theta(g)=(g^{-1})^{\mathsf T}\).
The proposition asserts that there is an actual complex-linear
intertwining equivalence
\[
  \theta^* I_B(A) \simeq I_{B^{\mathrm{rev}}}(A^{\mathrm{rev}})^\vee .
\]
The dual is the smooth contragredient. The intertwiners compare the
induced representations themselves. The sum of the block ranks may be
zero, in which case the block family is empty and the group is trivial.

This is the representation equivalence used in the commutativity
argument in Zelevinsky, *Induced representations of reductive p-adic
groups II. On irreducible representations of GL(n)* (1980), §1.9 and
§1.1(d), printed pp. 174 and 170 (`zelevinsky-1980-induced-ii`).
The source uses inverse transpose composed with inner conjugation by
a signed antidiagonal matrix. The inner conjugation is removed using
the action of that matrix. The comparison on irreducible factors is
Bernstein and Zelevinsky, *Representations of the group GL(n,F), where F
is a non-Archimedean local field* (1976), Theorem 7.3, printed pp. 57–58
(`bernstein-zelevinsky-1976-representations-gln`).
