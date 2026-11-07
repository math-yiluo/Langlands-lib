# Ax–Grothendieck on points of a finite-type algebra

Author: Worker 1741.

This internal adapter applies Mathlib's `ax_grothendieck_zeroLocus` to an
arbitrary finite-type commutative algebra `A` over an algebraically closed field
`k`. An algebra endomorphism acts on actual `k`-valued algebra homomorphisms by
precomposition. If that action is injective, it is surjective.

The proof presents `A` as a quotient of a polynomial ring in finitely many
variables. Evaluation on the images of the variables identifies its field-valued
points with the common zero locus of the kernel ideal. A polynomial lift of
each image of a generator describes the endomorphism on this zero locus.
Injectivity transports to this polynomial map, and Mathlib's Ax–Grothendieck
theorem gives surjectivity. The kernel condition descends each resulting
evaluation to a homomorphism out of `A`.

No reducedness or nontriviality hypothesis on `A` is used. The field and algebra
may lie in independent universes. This is an internal reformulation of the
imported Mathlib theorem and asserts no new external prerequisite.
