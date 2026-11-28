# Interpolation on determinant twists of Levi trace distributions

The determinant-order map takes a standard Levi product of general
linear groups over a nonarchimedean local field to one copy of
the integer lattice per block. It is locally constant, and its
pulled-back characters are exactly the unramified characters.
Continuous field automorphisms preserve the lattice coordinates. They
preserve the valuation order on nonzero elements and take any
uniformizer to another of order one. On the block scalar uniformizer
powers, the determinant-order map multiplies each coordinate by the
size of its block. It is therefore injective on that central lattice,
whose image has finite index.

`LeviDeterminantTwistInterpolationStatement` concerns finitely many
admissible irreducible representations of the Levi product and
arbitrary linear twisting endomorphisms. A complex linear functional
on distributions is regular on these families if its evaluations on
their twists have finite character expansions on the determinant
lattice. In this case, the functional agrees on all these twists
with evaluation at a single Schwartz–Bruhat test. The Levi product
is Hausdorff, locally compact, and totally disconnected with its Borel
structure. The trace uses the supplied left invariant measure finite
on compact sets.

Schur's lemma gives the scalar central action of each representation,
which induces the same covariance on its twisted distribution via
left translation of tests. Extend the inverse of this scalar
character along the injective degree map on the uniformizer lattice.
Twisting by the extension cancels the scalar action there and
multiplies each Laurent coefficient by the extension at its degree.
Finite twist interpolation applies to the normalized distributions,
and inverse twisting gives agreement on the original families.
This gives the central-character normalization used in the finite
orbit interpolation of Bernstein–Deligne–Kazhdan (1986), §4.2,
and the corresponding interpolation step for twisted traces in
Rogawski (1988), §11.
