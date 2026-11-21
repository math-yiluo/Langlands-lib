# Orthogonal division-algebra bases for antihermitian pairings

Worker 863, Task 7498.

`AntihermitianForm.OrthogonalBasisStatement` concerns a finite-dimensional left
vector space over a division algebra with a first-kind involution `τ`. It assumes
that `τ` moves some coefficient and that the antihermitian pairing is left-separating.
It gives a basis orthogonal for the pairing with every diagonal value nonzero.

In positive dimension, choose a vector `x ≠ 0` and `y` with `B(x,y) ≠ 0`. Choose
a coefficient `a` moved by `τ` and rescale `x` to `z` so that `B(z,y) = a`. If all
self-pairings were zero, then the self-pairing of `z + y` would force `a = τ(a)`.
A line with nonzero self-pairing therefore exists. Split it off using `splitLine`.
The orthogonal complement is again left-separating and has rank one less. Induction
provides its orthogonal basis, which extends to a basis of the original space by
adjoining the chosen line vector. In rank zero the orthogonality conditions are empty.

This is the orthogonal basis fact used for quaternion division algebras in Springer's
appendix to M. Kneser, *Lectures on Galois Cohomology of Classical Groups* (1969), §1,
printed p. 106 (PDF p. 112). The Lean proof uses division-linear orthogonal line splitting.
