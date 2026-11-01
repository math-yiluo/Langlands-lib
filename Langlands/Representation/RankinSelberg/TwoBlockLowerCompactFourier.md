# Compact-uniform lower partial Fourier bounds

This internal derived module makes the actual lower partial Fourier factor's
diagonal norm and endpoint support bounds uniform on compact right translates.
It then expresses them in the rotated standard torus coordinates used by the
lower quotient. The canonical p-adic topology, supplied character, supplied
self-dual scalar Haar measure and actual Schwartz–Bruhat row function remain
fixed throughout. The constants may depend on all these data and on the compact
set. No representation-dependent convergence threshold or outer absolute
integrability is asserted here.

`finite_rowTranslate_schwartz_range` lifts the published finite-range result
for the underlying translated functions to the Schwartz–Bruhat functions
themselves, using injectivity of the subtype coercion. This statement holds for
any topological field, any finite row dimension and any compact subset of the
general linear group. `partialSection_mul` moves the rightmost group factor
into the row test function, using the exact row-translation product identity.
It applies to the actual `partialSection`, retaining its scalar Haar measure.

`exists_partialSection_diagonal_compact_bounds` applies the diagonal bounds to
each of the finitely many translated Schwartz functions on a compact set `K`.
Upper bounds for the resulting finite families of real constants and natural
cutoffs give a single natural cutoff `M` and a positive constant `C`. The
constant is enlarged to at least one. Thus, for every unit diagonal vector `d`
and every `k ∈ K`, the norm of the partial section at `diagonalUnits d * k`
is at most `C * q ^ (sum i, natAbs (ord (d i)))`. A nonzero value forces
`ord (d (index 0 0)) ≤ M` and
`-M ≤ ord (d (index 1 (Fin.last (m 1))))`.
The finite-range argument also covers an empty compact set.

`blockRotation_inv_mul_diagonal` moves the inverse block rotation through a
diagonal matrix. It permutes the entries by the inverse of the published
`reversePermutation`. The proof checks the conjugation identity entrywise,
then multiplies by the inverse rotation on the right.
`exists_partialSection_rotated_diagonal_compact_bounds` applies the preceding
compact bound to the compact image `{blockRotation⁻¹ * k | k ∈ K}`.
Permutation invariance of the finite order sum gives the same norm exponent.
Both endpoint orders are evaluated at the corresponding inverse-permuted
diagonal coordinates. This proves the estimate for the exact representatives
`blockRotation⁻¹ * diagonalUnits d * k`.

`exists_partialSection_rotated_torus_compact_bounds` specializes the diagonal
entries to integer powers of the canonical `uniformizerUnit`. Its order is
one, so these orders are exactly the integer torus coordinates `lam i`.
For `j : Fin t` with `j.val = m 1`, the inverse block permutation sends the
original first-block first endpoint to `j.succ` and the original second-block
last endpoint to `j.castSucc`. Consequently, one positive `C` and natural `M`
work for all integer coordinate vectors `lam` and all `k ∈ K`:

- at `blockRotation⁻¹ * torus uniformizerUnit lam * k`, the partial section has
  norm at most `C * q ^ (sum i, natAbs (lam i))`;
- a nonzero value implies `lam j.succ ≤ M` and `-M ≤ lam j.castSucc`.

`RotatedTorusBoundData` stores the positive constant, cutoff and these exact
certificates. `rotatedTorusBoundData` chooses such a package from the proved
existence theorem under self-duality, compactness and the stated cut-index
hypothesis.

The provenance is internal: these are consequences of
`TwoBlockLowerDiagonalFourier`, the published finite-range smoothness of row
translates, the existing block-rotation conjugation formulas and canonical
uniformizer valuation identities. They introduce no new literature assertion,
choice of measure or convergence premise.
