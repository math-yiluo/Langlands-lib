# Meromorphic propagation of moving generalized exponent support

`MeromorphicExponentSupportStatement` uses a commutative group \(A\) acting by
evaluation shifts on the functions \(\mathbb C^X\). For a parameter
\(z\in\mathbb C^n\), write \(\phi_z\) for the function and
\(\chi_i(z):A\to\mathbb C\) for the finitely many permitted eigenvalue functions.
Each map \(z\mapsto\phi_z(x)\) and \(z\mapsto\chi_i(z)(a)\) is meromorphic
with a common open dense holomorphy domain \(D\).

On a nonempty open patch \(W\), suppose every \(\phi_z\) is a sum of joint
generalized eigenvectors for the permitted functions at \(z\). At any
\(z\in D\), in a supplied finite joint generalized exponent decomposition
of \(\phi_z\), every component whose eigenvalue function differs from all
\(\chi_i(z)\) vanishes.

For each permitted eigenvalue function, select a group element separating
its value from the unwanted eigenvalue function. On the seed patch, a
product of powers of the corresponding shift-minus-scalar operators
annihilates the family. The finite shift continuation gives one product
annihilating the continued family. The product preserves each joint
generalized eigenspace, so independence makes the unwanted term vanish
after applying the product. Each factor is injective on that term's joint
generalized eigenspace by the differing scalar values. This forces the term
itself to vanish.

This internal reduction is intended for the cuspidal exponent difference in
the Eisenstein functional equation.
