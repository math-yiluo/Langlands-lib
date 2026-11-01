# Compact representatives of archimedean connected components: proof

This module proves the published statement
`Langlands.Global.ArchimedeanGL.CompactComponentCoverageStatement K n`
from `Langlands.Global.ArchimedeanCompactComponentCoverageStatement`, for
every number field `K : Type u` in an arbitrary universe `u` and every
natural rank `n`, including `n = 0`. The theorem is

```
Langlands.Global.ArchimedeanGL.compactComponentCoverage
  (K : Type u) [Field K] [NumberField K] (n : ℕ) :
  CompactComponentCoverageStatement K n
```

It imports the statement unchanged. It changes no published file and adds
no hypothesis. The proof was written and checked by Worker 1169.

## The implemented proof

The proof works one place at a time over `𝕜 = ℝ` or `ℂ`, using Mathlib's
`RCLike` class. It then combines the places in mixed coordinates and moves
the result back to the completion-based group.

### One place: a path to a diagonal unitary matrix

`exists_unitary_mem_connectedComponent` states: for a finite index type `m`
and `A : Matrix.GeneralLinearGroup m 𝕜`, there is a `U` in the same group
whose matrix lies in `Matrix.unitaryGroup m 𝕜`, with
`A ∈ connectedComponent U`. For `𝕜 = ℝ`, `Matrix.unitaryGroup` is the full
orthogonal group.

1. **Gaussian elimination.** Mathlib's
   `Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec` writes
   `A = (L.map toMatrix).prod * diagonal D * (L'.map toMatrix).prod`. Here
   `L` and `L'` are lists of transvections `1 + c • single i j` with
   `i ≠ j`, and `D : m → 𝕜`. Transvections have determinant `1`, and
   `det A ≠ 0`, so every `D i` is nonzero.
2. **The path.** For real `s`, `scaleTransvection s T` multiplies the
   off-diagonal entry `c` of `T` by `s`. Put
   `r i s = Real.exp ((s - 1) * Real.log ‖D i‖)`, a positive real number,
   and
   `F s = (L.map (scaleTransvection s ·).toMatrix).prod *
   diagonal (fun i => D i * r i s) * (L'.map (scaleTransvection s ·).toMatrix).prod`.
   - Every scaled transvection still has determinant `1`, so
     `det (F s) = ∏ i, D i * r i s ≠ 0`.
   - Each entry of `F s` is a polynomial in `s` and the exponentials
     `r i s`, so `F` is continuous.
   - At `s = 1` the transvections are unchanged and `r i 1 = 1`, so
     `F 1 = A`.
   - At `s = 0` the transvections become `1` and `r i 0 = ‖D i‖⁻¹`, so
     `F 0 = diagonal (fun i => D i * ‖D i‖⁻¹)`.
     `diagonal_normalize_mem_unitaryGroup` shows that this matrix is
     unitary: each diagonal entry has absolute value `1`.
3. **Continuity into the units topology.** `unitOfDetNeZero F hF` views
   `F` as a map into `Matrix.GeneralLinearGroup m 𝕜`, using
   `Matrix.isUnit_iff_isUnit_det`. By `continuous_unitOfDetNeZero` this map
   is continuous for Mathlib's units topology. `Units.continuous_iff`
   requires both the matrix and its inverse to be continuous. The inverse is
   `(det (F s))⁻¹ • adjugate (F s)` (`Matrix.inv_def`). This is continuous
   because the determinant and the adjugate are continuous and the
   determinant never vanishes.
4. **Conclusion.** The image of `ℝ` under this continuous map is connected
   and contains `A` (at `s = 1`) and the unitary point `U` (at `s = 0`).
   Hence `A ∈ connectedComponent U`.

### All places at once, in mixed coordinates

`PlaceGL K n` is the product of `Matrix.GeneralLinearGroup (Fin n) ℝ` over
the real places with `Matrix.GeneralLinearGroup (Fin n) ℂ` over the complex
places, with the product topology.

- `assemble : PlaceGL K n → ArchimedeanGL K n` places the per-place
  matrices entrywise in `mixedEmbedding.mixedSpace K`, and does the same
  with their inverses. `assembleMatrix_mul` and `assembleMatrix_one` show
  that the result is a unit. `continuous_assemble` proves continuity in the
  units topology, again through `Units.continuous_iff`, because every entry
  of the matrix and of its inverse is a coordinate of a continuous
  per-place map.
- `places` sends `g : ArchimedeanGL K n` to its per-place matrices. It
  applies `Matrix.GeneralLinearGroup.map` along the projections to each
  real and each complex coordinate. `assemble_places` states that
  `assemble (places g) = g`.

`exists_compactFactors_mem_connectedComponent` says: for every
`g : ArchimedeanGL K n` there is `p : ArchimedeanCompactFactors K n` with
`g ∈ connectedComponent (ArchimedeanCompactFactors.toArchimedeanGL K n p)`.

To prove it, choose a unitary `U_v` for each place matrix of `g`, using the
one-place result. Mathlib's `connectedComponent_prod` and
`connectedComponent_pi` describe the connected component of a point in a
product. By them, `places g` lies in the connected component of the family
`(U_v)` in `PlaceGL K n`. The continuous map `assemble` sends connected
components into connected components
(`Continuous.image_connectedComponent_subset`). It sends `places g` to `g`
and the family `(U_v)` to `toArchimedeanGL` of the corresponding element
`p` of `ArchimedeanCompactFactors K n`; both equalities hold by definition
(`Units.ext` and `rfl`).

### Back to the completion-based group

Let `g : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)`.
Apply the previous step to `archimedeanGLCoordinates K n g` and obtain
`p`. The candidate is
`k = ⟨ArchimedeanCompactFactors.toInfiniteAdelicGL K n p, p, rfl⟩`, which
lies in `standardInfiniteCompact K n` because that subgroup is defined as
the range of `toInfiniteAdelicGL`. By definition, `toInfiniteAdelicGL K n p`
is `(archimedeanGLCoordinates K n).symm (toArchimedeanGL K n p)`. The
inverse coordinate map is continuous, so it sends the connected component
of `toArchimedeanGL K n p` into the connected component of `k`. It also
sends `archimedeanGLCoordinates K n g` back to `g`. Hence
`g ∈ connectedComponent k.val`.

The argument needs no case distinction. For `n = 0`, or for fields without
real or without complex places, the same steps apply verbatim: empty index
types give trivial products.

## Relation to the suggested route

The task suggested polar or QR decomposition. The implemented proof uses
neither. It deforms Mathlib's transvection–diagonal factorization instead:
the transvections are contracted to the identity and the diagonal entries
are rescaled to absolute value `1`. The resulting compact representative
is diagonal with entries of absolute value `1`. For a real place these
entries are `±1`.

## Scope

The helper declarations in this module are internal auxiliary results. They
are stated over arbitrary `RCLike` fields and finite index types, or for the
published mixed-coordinate group. The module keeps the published group
topology unchanged: the units topology over the entrywise topology of the
completion-based infinite adele ring. It also keeps the published
`standardInfiniteCompact K n`, with the full orthogonal groups at real
places and the unitary groups at complex places.

This theorem supplies component coverage only. It proves neither density
nor analytic uniqueness on the whole group. It proves no reproduction,
compact-type finiteness or growth statement. It does not count connected
components, does not assert that the group or the subgroup is connected,
and proves neither a polar nor a QR decomposition.
