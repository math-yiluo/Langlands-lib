# Proof of the Weyl-conjugated transpose transport of upper Bruhat cells

Author: Worker 915.

The theorem `Langlands.GeneralLinear.upperBruhatTranspose` proves exactly the
published proposition `Langlands.GeneralLinear.UpperBruhatTransposeStatement.{u}`
from `Langlands.Group.GL.UpperBruhatTransposeStatement`. The module imports only
that statement module, which is used unchanged together with everything it
imports. The proof keeps the whole statement: every natural rank `n`, including
`0`, every permutation `w`, every bound `k : ℕ`, and every commutative ring
`R : Type u` with a topology making it a topological ring. No field,
nontriviality, Hausdorff, local compactness or positive-rank hypothesis is used.
The proof assumes no inversion-count equality, cell image, layer image, Bruhat
decomposition or cell disjointness. The only axioms are Lean's standard
`propext`, `Classical.choice` and `Quot.sound`.

Throughout, `tau` is the statement's homeomorphism
`(transposeHomeomorph n R).trans (conjugationHomeomorph (weylLong n R))`, and
`T w = upperBruhatTransposeIndex n w = Fin.revPerm * w⁻¹ * Fin.revPerm`.

## Named results

All names are in `Langlands.GeneralLinear`. The helper theorems are stated with
the full expression for `tau`; no new definition is introduced.

| Theorem | Content |
| --- | --- |
| `permutationInversionCount_upperBruhatTransposeIndex n w` | `permutationInversionCount n (T w) = permutationInversionCount n w` (count clause) |
| `image_eq_of_involutive_of_image_subset` | for involutions `f` and `T`, inclusions `f '' S i ⊆ S (T i)` for all `i` are equalities |
| `weylConjugateTranspose_apply n R g` | `tau g = weylLong n R * transposeHomeomorph n R g * weylLong n R` |
| `weylConjugateTranspose_entry n R g i j` | `tau g i j = g j.rev i.rev` |
| `weylConjugateTranspose_involutive n R` | `tau (tau g) = g` |
| `weylConjugateTranspose_mul n R g h` | `tau (g * h) = tau h * tau g` |
| `weylConjugateTranspose_mem_upperTriangular n R` | `tau` maps `upperTriangularSubgroup n R` into itself |
| `weylConjugateTranspose_permutation n R w` | `tau (permutation n R w) = permutation n R (T w)` |
| `weylConjugateTranspose_image_upperBruhatCell_subset n R w` | `tau '' upperBruhatCell n R w ⊆ upperBruhatCell n R (T w)` |
| `weylConjugateTranspose_image_upperBruhatCell n R w` | first cell equality |
| `weylConjugateTranspose_image_upperBruhatLayerLE n R k` | layer equality |
| `weylConjugateTranspose_image_upperBruhatHigherCells n R w` | higher-cell equality |
| `weylConjugateTranspose_image_upperBruhatCellNeighborhood n R w` | neighborhood equality |

The final theorem `upperBruhatTranspose` supplies the count theorem as the first
conjunct; for the second it introduces `R`, its instances, `n`, `w`, `k` and the
`let`-bound `tau`, and returns the four image equalities above.

## Count clause

The published `permutationInversionCount_eq_fintypeCard` rewrites both counts as
cardinalities of subtypes of inverted ordered pairs `(i, j)`, with `i < j` and
`v j < v i`. By `upperBruhatTransposeIndex_apply`, `T w a = (w⁻¹ a.rev).rev`.
The proof gives an explicit equivalence of these subtypes (`Fintype.card_congr`):

- an inverted pair `(a, b)` of `T w` goes to `(w⁻¹ a.rev, w⁻¹ b.rev)`;
- an inverted pair `(x, y)` of `w` goes back to `((w x).rev, (w y).rev)`.

Since `Fin.rev` reverses the order (`Fin.rev_lt_rev`), the condition
`T w b < T w a` is `w⁻¹ a.rev < w⁻¹ b.rev`, and `a < b` is
`w (w⁻¹ b.rev) < w (w⁻¹ a.rev)`; so the image is an inverted pair of `w`.
Conversely `w y < w x` gives `(w x).rev < (w y).rev`, and `x < y` gives the
inversion of `T w` at `((w x).rev, (w y).rev)`. The two maps are mutually
inverse by `Fin.rev_rev` and `w (w⁻¹ z) = z`. Both ranks `0` and positive are
covered, since nothing depends on `n`.

## Properties of `tau`

By `Homeomorph.trans_apply`, `conjugationHomeomorph_apply` and the published
`weylLong_inv`, `tau g = weylLong * transposeHomeomorph g * weylLong`. The
published `weylLong_conjugate_entry` and `transposeHomeomorph_entry` then give
`tau g i j = g j.rev i.rev`. Hence:

- `tau` is involutive: applying the entry formula twice and `Fin.rev_rev` gives
  equal entries, and `Units.ext` with matrix extensionality gives `tau (tau g) = g`.
- `tau` reverses products: `transposeHomeomorph_mul` gives
  `(g h)ᵀ = hᵀ gᵀ`, and inserting `weylLong * weylLong = 1`
  (`weylLong_mul_self`) gives `tau (g h) = tau h * tau g`.
- `tau` preserves the upper triangular subgroup: if `b` vanishes below the
  diagonal and `j < i`, then `i.rev < j.rev`, so the entry
  `tau b i j = b j.rev i.rev` lies below the diagonal of `b` and is `0` by
  `mem_upperTriangularSubgroup_iff`.
- `tau` sends permutation matrices to permutation matrices: by
  `transposeHomeomorph_apply`, the transpose of `permutation n R w` is
  `inverseTranspose n R (permutation n R w)⁻¹`; `permutation_inv` and
  `inverseTranspose_permutation` identify it with `permutation n R w⁻¹`, that
  is `(permutation n R w)⁻¹`. The published homomorphism law
  `permutation_upperBruhatTransposeIndex` states
  `permutation n R (T w) = weylLong * (permutation n R w)⁻¹ * weylLong`, which
  is exactly `tau (permutation n R w)`.

## Cell, layer, higher-cell and neighborhood equalities

Cell inclusion. If `g = b₁ * permutation n R w * b₂` with `b₁`, `b₂` upper
triangular, then anti-multiplicativity gives
`tau g = tau b₂ * permutation n R (T w) * tau b₁`, and `tau b₂`, `tau b₁` are
upper triangular. So `tau '' upperBruhatCell n R w ⊆ upperBruhatCell n R (T w)`.

From inclusions to equalities. The general lemma
`image_eq_of_involutive_of_image_subset` takes an involution `f` of a type, an
involution `T` of an index type and a family `S` with `f '' S i ⊆ S (T i)` for
every index `i`. For `x ∈ S (T i)`, the inclusion at the index `T i` and
`T (T i) = i` give `f x ∈ S i`, and `f (f x) = x`; hence `x ∈ f '' S i`. It is
applied with `f = tau` (involutive, above) and the published involution
`upperBruhatTransposeIndex_involutive`.

- Cells: the cell inclusion for every permutation gives
  `tau '' upperBruhatCell n R w = upperBruhatCell n R (T w)`.
- Layers: if `g ∈ upperBruhatCell n R v` with
  `permutationInversionCount n v ≤ k`, then `tau g` lies in the cell of `T v`,
  and `T v` has the same count, so `tau g ∈ upperBruhatLayerLE n R k`. The
  general lemma with the constant family over `Unit` and `T = id` gives
  `tau '' upperBruhatLayerLE n R k = upperBruhatLayerLE n R k`.
- Higher cells: if `g ∈ upperBruhatCell n R v` with
  `permutationInversionCount n w < permutationInversionCount n v`, then
  `tau g` lies in the cell of `T v`, and rewriting both counts with the count
  clause gives
  `permutationInversionCount n (T w) < permutationInversionCount n (T v)`.
  This is the inclusion into `upperBruhatHigherCells n R (T w)` for every `w`,
  and the general lemma gives the equality.
- Neighborhoods: `upperBruhatCellNeighborhood` is the union of the cell and
  the higher cells, and `Set.image_union` with the two previous equalities
  gives the neighborhood equality.

## Scope

This proves only the finite algebraic transport stated in
`UpperBruhatTransposeStatement`. As documented with the statement, the map is
the `h₀`-free map `g ↦ w₀ gᵀ w₀`, not Shalika's twisted anti-automorphism
`θ`, and the layers are indexed by the published inversion count, not by
analytic dimension. No claim is made about distributions, about individual cells
being fixed, or about topological properties of the cells.
