# Matrix conjugacy in a squarefree characteristic-polynomial fiber

This algebraic lemma supplies the ordinary conjugacy input to the forward
reduction of Henniart–Lemaire (2011), II.2.11. It is a consequence of the
structure theorem for finite torsion modules over the polynomial ring of a field.
The proof applies to any squarefree characteristic polynomial. In particular, it
applies at the regular semisimple elements used by the reduction.

Cayley–Hamilton annihilates the polynomial module of a matrix. The Library's
bounded cyclic decomposition writes this module as a finite product of principal
quotients. Multiplication by the polynomial variable on each factor has
characteristic polynomial equal to its monic defining polynomial, by the power
basis of the quotient. The block product formula shows that the product of those
defining polynomials is the characteristic polynomial of the original matrix.

Squarefreeness makes the defining polynomials pairwise coprime. The Chinese
remainder theorem identifies the product of quotients with the single principal
quotient by the characteristic polynomial. Matrices with the same squarefree
characteristic polynomial therefore have isomorphic polynomial modules. The
Library's polynomial-module conjugacy theorem gives a conjugating matrix.
