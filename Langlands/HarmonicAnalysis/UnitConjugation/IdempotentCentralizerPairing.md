# Invariant pairings and the idempotent decomposition

Let `A` be an algebra over a field `F`, and let `e` be an idempotent. Put
`f = 1 - e` and `M = Subalgebra.centralizer F {e}`. The map
`cornerProjection F e` sends `x` to `e x f`, and `offDiagonalCorner F e`
is its image `e A f`. The opposite corner is `offDiagonalCorner F f = f A e`.
The identity `diagonal_add_corners` writes every element of `A` as the sum
of its diagonal part and the two corner projections.

Suppose that `F` has characteristic zero and `B` is an `IsInvariantPairing`.
Conjugation by `2 e + f` fixes `M` and multiplies `e A f` by `2`.
Invariance of `B` and bilinearity give `B(M, e A f) = 0` and
`B(e A f, e A f) = 0` in `pairing_centralizer_corner_eq_zero` and
`pairing_corner_eq_zero`. Applying the same argument to `f` gives the
corresponding identities for `f A e`, since `e` and `f` have the same
centralizer.

The theorem `invariantPairing_centralizer` equips the restricted form on `M`
with `IsInvariantPairing`. The orthogonality identities and the decomposition
of an arbitrary element show that the restriction is nondegenerate.
Symmetry is inherited from `B`, and conjugation invariance follows from the
inclusion `Mˣ → Aˣ`. The theorem `opposite_corner_nondegenerate` applies the
same decomposition to prove that the bilinear map `e A f × f A e → F`
induced by `B` is nondegenerate on both sides.

For `X, Y ∈ M`, `Z, W ∈ e A f` and `W′ ∈ f A e`, expanding by bilinearity
gives `pairing_add_corners`.

\[
 B(X+Z, Y+W+W') = B(X,Y) + B(Z,W').
\]

This is the pairing identity for the Fourier kernel in Harish-Chandra,
*Admissible invariant distributions on reductive p-adic groups*, notes by
DeBacker and Sally, ULS 16, 1999, §1.2, Lemma 1.4, printed pp. 6–7. The source
uses the Lie algebras of the Levi and the two opposite unipotent radicals.
For the block triangular parabolics of `Aˣ`, these are `M`, `e A f` and `f A e`.
The source uses nondegeneracy on the opposite radicals in the determinant
comparison on printed p. 8. The Lean results use only the algebra, field and
pairing assumptions above.
