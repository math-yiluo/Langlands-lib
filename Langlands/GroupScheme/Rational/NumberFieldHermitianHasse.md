# The Hasse kernel for special unitary matrix groups

`NumberFieldHermitianHasseStatement` concerns a group with an actual all-test special unitary matrix presentation by a nonsingular Hermitian form of positive dimension over a separable quadratic extension of a number field. A cocycle on any finite Galois field cover that becomes trivial on the full pullback at every completion is trivial on the original cover.

Finite-algebra Hilbert 90 supplies an ambient unit primitive and descends the inverse Gram matrix. Each local trivialization yields congruence of the inverse Gram matrices over the full completion coefficient algebra. Hermitian local-to-global congruence yields the corresponding change of basis over the quadratic field, which corrects the primitive to a unitary one. The determinant-one cocycle equations make the primitive's determinant Galois fixed. It descends to a unit of conjugate norm one in the quadratic field. Scaling one line of an orthogonal basis realizes that determinant. The inverse of this isometry, extended to the original cover, corrects the primitive to determinant one without changing its coboundary.

This is the Hermitian matrix case of the unitary Hasse principle in Kneser, *Lectures on Galois Cohomology of Classical Groups*, §5.5. The congruence theorem in the Lean proof uses the already proved quadratic Hasse–Minkowski isometry theorem.
