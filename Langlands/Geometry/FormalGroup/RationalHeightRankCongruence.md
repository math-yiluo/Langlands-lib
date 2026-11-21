# Rank congruence for equivariant equations

This module proves an auxiliary finite-algebra lemma for
`RationalHeightFieldRank`. Let \(F_i\) be one polynomial per variable, each
of weight \(c\) under diagonal scaling, for \(c\ne 0\). At widths \(n\) and
\(m\) with \(2n\le m\), suppose the two quotients by the truncated equations
have the same dimension \(D\).

Choose \(L\ge m\) larger than the total degrees of all \(F_i\) and satisfying
\(c^L=c\). Adjoin the term \(X_i^L\) to each \(F_i\). In the new quotient
algebra \(B\), the box monomials with all exponents less than \(L\) form a
basis. This follows by graded-lex division and the coprime leading monomials
\(X_i^L\), using the Library's `CoprimeGroebner` lemma. Diagonal scaling
descends to an automorphism of \(B\). The two box ideals at widths \(n\) and
\(m\) give quotients of dimension \(D\), so they coincide. Their common ideal
is idempotent since the \(m\)-th powers are in the square of the width-\(n\)
ideal. It equals the box ideal at every width at least \(n\), by applying
idempotence in the quotients where the ideal of the variables is nilpotent.

For a variable image \(x\), take a large power of \(x\) whose principal ideal
\(W\) has stabilized. Multiplication by \(x\) on \(W\) is invertible and
conjugation by the scaling automorphism multiplies this operator by \(c\).
Taking determinants gives \(c^{\dim W}=1\), so quotienting by \(W\) preserves
dimension modulo the order of \(c\). Iterating over the variables in
successive quotients yields a quotient by individual powers whose ideal is
between two equal box ideals. Its dimension is \(D\).
`finrank_modEq_of_equivariant_equations` therefore compares \(D\) with
\(L^{\#\{\text{variables}\}}\) modulo the order of \(c\).

## Diagonal weights of a common order

`diagonalScale` permits a separate nonzero weight for each polynomial
variable. `finrank_modEq_of_diagonal_equations` assumes that the equation
paired with a variable has that variable's weight and that these weights
have a common multiplicative order. The perturbation still adds the same
power of each variable. In the determinant step, quotienting by a
stabilized power of one variable uses its own eigenvalue. Its order is the
common modulus, so the dimension comparison survives each quotient. The
original uniform-weight theorem follows by taking constant diagonal weights.

This generalization supplies the finite-kernel rank calculation when the
unramified division subfield acts through the distinct special tangent
characters in Drinfeld 1976, §2A, printed p. 109. A generator of the residue
units has the same order in each of those characters.
