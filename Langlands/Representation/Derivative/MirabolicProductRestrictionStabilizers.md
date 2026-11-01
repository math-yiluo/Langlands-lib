# The two orbit stabilizers are the mixed-product inducing subgroups

Author: Worker 1163.

This helper module of the proof of
`Langlands.Derivative.MirabolicProductRestrictionStatement` identifies the
stabilizers of the two orbit representatives of
`Derivative.MirabolicProductRestrictionOrbits` with the published inducing
subgroups of the mixed products, and identifies the Levi part of the conjugated
element with the published mixed-product projections. These are entrywise
matrix computations, internal to the proof.

The stabilizer of the representative `w` is the published
`Geometric.orbitStabilizer P Q w`, the subgroup of `q ∈ Q` with
`w⁻¹ q w ∈ P`, and `Geometric.stabilizerToInducing P Q w` sends it to
`w⁻¹ q w ∈ P`.

## The closed orbit (representative `1`)

- `leftIndex_inl_eq`, `leftIndex_inr_eq`: the published case (II) coordinates
  `leftIndex (m+1) n` are `castAdd` on the first block and `natAdd` on the
  second.
- `mem_closedStabilizer_iff`: `q ∈ orbitStabilizer P Q 1` iff `q` lies in the
  published `leftSubgroup (m+1) n` (both say that the lower-left block vanishes).
- `closedStabilizer_levi_zero`, `closedStabilizer_levi_one`: the binary Levi
  projection of `stabilizerToInducing P Q 1 q = q` has blocks the two components
  of the published `leftProjection q` (the `GL_(m+1)` block and the underlying
  matrix of the `P_(n+1)` block).

## The open orbit (representative `w = openRep`)

- `openCast m n : P_((m+1)+n+1) ≃ₜ* P_((n+1)+m+1)` is the rank identification
  `mirabolicCast` of the cast module for `(n + 1) + m = (m + 1) + n`, and
  `openCast_apply` reads its entries at cast indices.
- `mem_openStabilizer_iff`: `q ∈ orbitStabilizer P Q w` iff `openCast q` lies in
  the published `rightSubgroup (n+1) m`. Both conditions say that the entries of
  `q` at `(openIndex (natAdd i), openIndex (castAdd j))` vanish, by
  `openRep_conj_apply`.
- `openStabilizer_levi_zero`, `openStabilizer_levi_one`: the binary Levi
  projection of `w⁻¹ q w` has blocks the underlying matrix of the mirabolic
  component and the `GL_(n+1)` component of the published
  `rightProjection (openCast q)`.

Thus the stabilizer of the open orbit, carried to `P_((n+1)+m+1)`, is the case
(III) subgroup with mirabolic block the first `m` and the last coordinates, and
`GL_(n+1)` block the middle coordinates.

## Imports

`Derivative.MirabolicProductRestrictionCasts` (for `mirabolicCast`) and
`Derivative.MirabolicProductRestrictionOrbits`.
