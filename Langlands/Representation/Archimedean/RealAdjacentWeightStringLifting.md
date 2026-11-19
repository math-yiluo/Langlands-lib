# One-sided Fourier lifting on an adjacent weight string

`RealAdjacentWeightStringLiftingStatement` concerns two abstract adjacent rotation
generators `a` and `b` on a finite-dimensional complex space with the two
specified commutator identities. The finite `a`-mode decomposition has support
at most `J` and mode spaces of dimension at most one. The raising operator is
injective on the mode spaces below `J`, and the normalized adjacent operator
`-I • b` has every integer eigenvalue from `-J` to `J`. For a positive integer
`N` and natural number `H`, suppose the degree-`H` differential tail polynomial
in `-I • b` sends `v` to a vector with zero modes at indices `i ≥ N+H`. Then
some vector in the kernel of that polynomial agrees with `v` at all `i ≥ N`.

The result is derived from the adjacent commutators and mode decomposition in
`RealOrthogonalUncertainty` and the falling factorial in
`RealTailMultiplierPolynomial`. The operator `-I • b` shifts each mode by one
in either direction. For an input supported at or below `m`, the coefficient
at `m+d` of its `d`th power uses only the term that raises at every step. All
lower powers vanish there. If the input at `m` and the polynomial's leading
coefficient are nonzero and `m+d ≤ J`, injectivity along the raising chain
makes the output at `m+d` nonzero.

For `N ≤ J`, set `r = min(H, J−N+1)`. The Lean proof chooses `r` distinct
integer roots of the tail polynomial in `[-J,J]` from the progression
`2k−H+1` with `0 ≤ k < H`. For `H ≤ J+1` the entire progression lies in the
interval. For `H > J+1` the chosen part starts at `-J` or `-J+1`, and `N > 0`
ensures `r ≤ J`. One eigenvector for each chosen root gives an
`r`-dimensional subspace of the polynomial kernel. Its map to the product
of the highest `r` mode spaces is injective. A nonzero vector in its
kernel would have highest mode `m ≤ J−r`, so the monic product of the
linear factors of those roots would give a nonzero output at `m+r`.
That product kills the span by the eigenvector equation. The product of
the mode spaces has dimension at most `r`, so the coordinate map is
surjective. This produces a kernel vector `w` matching the highest `r`
coordinates of `v`.

If `v−w` has a nonzero mode at or above `N`, its highest mode `m` satisfies
`N ≤ m ≤ J−r`. This forces `r = H`. The tail polynomial then gives a
nonzero coefficient at `m+H`, in contradiction to the input hypothesis
and the kernel equation for `w`. For `J < N` the zero vector is a lift.
The application to compact representations requires a decomposition with
the stated weight-string properties.
