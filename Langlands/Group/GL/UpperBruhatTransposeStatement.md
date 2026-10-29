# Weyl-conjugated transpose of actual upper Bruhat cells and inversion layers

Author: Worker 915.

This module defines one proposition,
`Langlands.GeneralLinear.UpperBruhatTransposeStatement.{u}`, a transparent `def`
returning `Prop`. It states that the published transpose index preserves the
inversion count, and how the published Weyl-conjugated transpose acts on the
actual upper Bruhat cells and their inversion unions. The module proves none of
these claims; the proof is a separate task. It imports
`Langlands.Group.GL.UpperBruhatFiltration` and
`Langlands.HarmonicAnalysis.Distribution.GeneralLinear` unchanged.

## Existing constructions used

No new set, cell, permutation, map or homeomorphism is constructed. The
statement uses only these published declarations:

- `upperBruhatCell n R w`, from `Langlands.Group.GL.UpperBruhatCells`: the set of
  `g` in `Langlands.GeneralLinear n R` (Mathlib's group of invertible
  `n × n` matrices over `R`) of the form `b₁ * permutation n R w * b₂` with `b₁`
  and `b₂` in `upperTriangularSubgroup n R`, that is, the actual double coset
  `B p_w B`. Membership in `upperTriangularSubgroup n R` means
  `g i j = 0` whenever `j < i`.
- `permutation n R w`, from `Langlands.Group.GL.Maps`: the permutation matrix
  sending the standard basis vector `e_j` to `e_(w j)`, so its entry `(i, j)` is
  `1` if `w j = i` and `0` otherwise. `weylLong n R` is
  `permutation n R Fin.revPerm`, the matrix with ones on the anti-diagonal.
- From `Langlands.Group.GL.UpperBruhatFiltration`:
  - `permutationInversionCount n w`, the number of ordered pairs
    `(i, j) : Fin n × Fin n` with `i < j` and `w j < w i`. It is defined as
    `relationInversions (fun a b : Fin n => b < a) (List.ofFn ⇑w)`, and the
    published lemma `permutationInversionCount_eq_card_permutationInversions`
    identifies it with this ordered-pair count.
  - `upperBruhatTransposeIndex n w`, the permutation
    `Fin.revPerm * w⁻¹ * Fin.revPerm`. In `Equiv.Perm` the product is
    composition, so it sends `i` to `(w⁻¹ i.rev).rev`, where `i.rev` is
    `n - 1 - i`.
  - `upperBruhatLayerLE n R k`, the union of the cells `upperBruhatCell n R v`
    over the permutations `v` with `permutationInversionCount n v ≤ k`.
  - `upperBruhatHigherCells n R w`, the union of the cells
    `upperBruhatCell n R v` over the permutations `v` with
    `permutationInversionCount n w < permutationInversionCount n v` (strict).
  - `upperBruhatCellNeighborhood n R w`, the union
    `upperBruhatCell n R w ∪ upperBruhatHigherCells n R w`.
- `Langlands.HarmonicAnalysis.Distribution.transposeHomeomorph n R`, from
  `Langlands.HarmonicAnalysis.Distribution.GeneralLinear`: actual matrix
  transposition as a homeomorphism of `Matrix.GeneralLinearGroup (Fin n) R`.
  Its published lemma `transposeHomeomorph_coe` says that the underlying matrix
  of its value at `g` is `gᵀ`.
- `Langlands.HarmonicAnalysis.Distribution.conjugationHomeomorph a`, from
  `Langlands.HarmonicAnalysis.Distribution.Basic`: the inner automorphism
  `x ↦ a * x * a⁻¹` as a homeomorphism (`conjugationHomeomorph_apply`).

## The map

Inside the statement the homeomorphism of `Langlands.GeneralLinear n R` is
bound by a `let`:

```lean
tau :=
  (Langlands.HarmonicAnalysis.Distribution.transposeHomeomorph n R).trans
    (Langlands.HarmonicAnalysis.Distribution.conjugationHomeomorph
      (weylLong n R))
```

`Homeomorph.trans` applies `transposeHomeomorph` first, so
`tau g = weylLong n R * gᵀ * (weylLong n R)⁻¹`. By the published lemma
`weylLong_inv`, `(weylLong n R)⁻¹ = weylLong n R`, so the actual formula is
`g ↦ weylLong * gᵀ * weylLong`. Its entry `(i, j)` is `g j.rev i.rev`: the
published lemma `weylLong_conjugate_entry` (in `Langlands.Group.GL.Maps`) gives
`(weylLong n R * h * weylLong n R) i j = h i.rev j.rev`, and
`transposeHomeomorph_entry` gives `transposeHomeomorph n R g i j = g j i`.

Positive-rank bridge. For `n = m + 1` the displayed homeomorphism is
definitionally `Langlands.Whittaker.weylTransposeHomeomorph m R` from
`Langlands.Representation.Whittaker.Distribution`: the body of that definition is
exactly `(transposeHomeomorph (m + 1) R).trans
(conjugationHomeomorph (weylLong (m + 1) R))`. This module does not import that
file and adds no bridge declaration; the statement is written with the
rank-general expression so that it also covers rank zero.

## The statement

`UpperBruhatTransposeStatement.{u}` is the conjunction of two clauses.

1. Count clause. For every natural number `n`, including `0`, and every
   `w : Equiv.Perm (Fin n)`,

   ```lean
   permutationInversionCount n (upperBruhatTransposeIndex n w) =
     permutationInversionCount n w
   ```

   This clause involves no ring and no topology.

2. Cell clauses. For every `R : Type u` with `[CommRing R]`,
   `[TopologicalSpace R]` and `[IsTopologicalRing R]`, every natural number `n`,
   including `0`, every `w : Equiv.Perm (Fin n)` and every `k : ℕ`, with `tau`
   as above, the following four equalities of subsets of
   `Langlands.GeneralLinear n R` hold, where `tau '' S` is the image of `S`:

   ```lean
   tau '' upperBruhatCell n R w =
     upperBruhatCell n R (upperBruhatTransposeIndex n w)
   tau '' upperBruhatLayerLE n R k = upperBruhatLayerLE n R k
   tau '' upperBruhatHigherCells n R w =
     upperBruhatHigherCells n R (upperBruhatTransposeIndex n w)
   tau '' upperBruhatCellNeighborhood n R w =
     upperBruhatCellNeighborhood n R (upperBruhatTransposeIndex n w)
   ```

   In words: `tau` maps the actual cell of `w` onto the actual cell of the
   transpose index of `w`; it maps every inversion layer onto itself; and it
   maps the union of cells with strictly more inversions than `w`, and the cell
   neighborhood of `w`, onto the corresponding sets for the transpose index.

Scope. The ring `R` lives in an arbitrary universe `u` and is any commutative
ring. It need not be a field, nontrivial, Hausdorff or locally compact. The
topology hypotheses are present only because `transposeHomeomorph` and
`conjugationHomeomorph` are homeomorphisms and require them; the four
equalities concern set images and no topological property. The statement does
not assert that any individual cell is fixed by `tau`: the cell of `w` is sent
to the cell of `upperBruhatTransposeIndex n w`, which in general differs from
`w`. No hypothesis of the proposition contains inversion preservation, a cell
image, a layer image, a Bruhat decomposition or disjointness of cells.

## Source and provenance

Provenance: internal. The registered original is
`shalika-1974-multiplicity-one`, J. A. Shalika, *The multiplicity one theorem
for GLn*, Ann. of Math. (2) 100 (1974), 171–193, retained at
`/home/taskhub/central-library/Shalika--The multiplicity one theorem for GLn--1974.pdf`
with SHA256
`788c5d124024c768aa47c4e8b179475fbcf5b0882a518ae60b19cdc88089f087`. Printed
pp.174, 175, 178 and 179 (one-based PDF pages 5, 6, 9 and 10) were read. No
errata note for this source exists in the project or Library notes, and a web
search on 2026-10-28 found no published erratum.

- Printed p.174 defines, for `x ∈ G = GL_n(k)`, the anti-automorphism
  `θ(x) = w₀ h₀ ᵗx h₀⁻¹ w₀⁻¹`, the transpose conjugated by `w₀ h₀` (in the scan
  the transposed letter resembles `u`; the variable being defined is `x`). Here
  `w₀` is the long Weyl element and `h₀` is a fixed diagonal element chosen from
  the character `χ`. The page lists the properties (1.1)–(1.5) of `θ` and
  names the double cosets `G_w = HUwU`. `HU` is the upper triangular
  subgroup, so `upperBruhatCell n R w` is the analogue over `R` of this double
  coset, for the published permutation matrix.
- Printed p.175 (Lemma 1.7 and its Corollary, over local fields) defines `Ω_w`
  as the union of `G_w` with the double cosets of strictly larger dimension.
- Printed pp.178–179 order the double cosets by dimension, form the unions
  `ω_j` of the double cosets of dimension `≤ r_j`, and prove Theorem 1.6 by
  induction over these layers (Lemma 1.16, Proposition 1.17).

This statement is not a verbatim source theorem and makes no assertion about
distributions or their invariance. It is a finite algebraic adapter motivated
by that discussion, for the later dimension-layer argument. Its differences
from the source are deliberate:

- `tau` omits Shalika's diagonal twist `h₀`; it is the `h₀`-free map
  `g ↦ w₀ gᵀ w₀`.
- Cells are indexed by the inversion count of the published permutation, not by
  analytic dimension, and the unions are the published inversion unions. This
  module does not compare them with Shalika's `ω_j` or `Ω_w`.
- The ring is an arbitrary commutative topological ring rather than a local
  field.

## Status

This is a statement only. It contains no proof, no `sorry`, no `admit` and no
new axiom, and nothing in the Library proves it at the time of submission.
