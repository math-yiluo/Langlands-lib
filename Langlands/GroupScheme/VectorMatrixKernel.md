# Actual scheme kernels of square matrix maps over fields

The actual scheme-theoretic kernel of every square matrix homomorphism between
polynomial vector groups over a field is isomorphic, over that same field, to
a polynomial vector group. The chosen dimension in `matrixKernelDimension`
and the isomorphism in `matrixKernelIso` are noncanonical.

The proof uses Mathlib's decomposition of a square field matrix into a product
of elementary transvections, a diagonal matrix, and a second product of
elementary transvections. The two products are invertible: their inverses are
the reversed products of inverse transvections. The matrix-map composition
formula therefore gives an isomorphism of arrows from the original map to the
diagonal map. The induced isomorphism of actual kernels is composed with the
existing diagonal-kernel isomorphism. That diagonal kernel is a vector group
on the indices whose coefficients vanish. All these are group-scheme
isomorphisms on every scheme test, including nonreduced tests.

Consequently the actual kernel is smooth, connected, and unipotent. The same
three properties hold after any ring-to-field specialization of a square
coefficient matrix, by the matrix-map base-change formula and transport of
actual kernels. The specialized matrix may have any rank; no reduced-test or
rational-point criterion is substituted for a scheme kernel.

This is an internal linear-algebra and group-scheme argument supporting the
additive transition calculation in Kaletha–Prasad, *Bruhat–Tits theory:
a new approach* (2023), Section C.2, printed pp.697–698 (PDF pp.728–729).
It does not supply an actual root-depth integral model, a supplied apartment
comparison, or the full C.5.3 theorem.
