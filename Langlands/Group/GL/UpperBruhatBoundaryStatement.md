# Strict inversion decrease on boundaries of actual upper Bruhat cells

Author: Worker 913.

`Langlands.GeneralLinear.UpperBruhatBoundaryStatement.{u}` is a closed,
transparent `Prop`-valued definition in
`Langlands.Group.GL.UpperBruhatBoundaryStatement`. This module states the
proposition only; it provides no proof of it. The proposition is unproved here,
and its proof is a separate later obligation.

## Exact proposition

The proposition is

```text
∀ (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
  [T2Space K] (n : ℕ) (w : Equiv.Perm (Fin n)),
  closure (upperBruhatCell n K w) \ upperBruhatCell n K w ⊆
    {g | ∃ v : Equiv.Perm (Fin n),
      permutationInversionCount n v < permutationInversionCount n w ∧
      g ∈ upperBruhatCell n K v}
```

Thus it ranges over every field `K` in the universe `u` and every topology on
`K` for which `K` is a topological division ring (continuous addition, negation,
multiplication and inversion away from zero) and which is Hausdorff. It ranges
over every natural rank `n`, including `n = 0`, and every permutation `w` of
`Fin n`. All these quantifiers are inside the proposition. No positivity,
nontriviality, characteristic, valuation, completeness or local compactness
hypothesis occurs.

In words: every point of the closure of the actual cell `C_w` that is not in
`C_w` itself lies in some actual cell `C_v` whose permutation `v` has strictly
fewer inversions than `w`. The inequality
`permutationInversionCount n v < permutationInversionCount n w` is strict, on
natural numbers.

`closure` is Mathlib's topological closure, and `\` is set difference. Both are
taken in the ambient group `Langlands.GeneralLinear n K`, that is
`Matrix.GeneralLinearGroup (Fin n) K`, the units of the matrix ring. Its
topology is the existing inherited one, Mathlib's `Units.instTopologicalSpaceUnits`
on `(Matrix (Fin n) (Fin n) K)ˣ`. That topology is induced by
`g ↦ (g, op g⁻¹)` into the product of the matrix space with its opposite, where
matrices carry the entrywise product topology. The closure is therefore taken
inside the invertible matrices, not in the space of all matrices. No other
topology, quotient or abstract model of the cells enters the statement.

## The cells and the inversion count

Both ingredients are imported unchanged.

`upperBruhatCell n K w`, from `Langlands.Group.GL.UpperBruhatCells`, is the
actual subset

```text
{g | ∃ b₁ ∈ upperTriangularSubgroup n K,
       ∃ b₂ ∈ upperTriangularSubgroup n K, g = b₁ * permutation n K w * b₂}
```

of `Langlands.GeneralLinear n K`. Here `upperTriangularSubgroup n K` is the
subgroup of invertible matrices whose entries `(i,j)` with `j < i` vanish. The
matrix `permutation n K w` has entry `(i,j)` equal to `if w j = i then 1 else 0`,
so it sends `e_j` to `e_(w j)`. The statement neither reverses `w` nor changes
the subgroup, the cells or their topology.

`permutationInversionCount n w`, from `Langlands.Group.GL.UpperBruhatFiltration`,
is `relationInversions (fun a b : Fin n => b < a) (List.ofFn ⇑w)`. By the
published adapter `permutationInversionCount_eq_card` it equals the number of
ordered pairs `(i, j) : Fin n × Fin n` with `i < j` and `w j < w i`.

The right-hand side is the union of the actual cells with strictly fewer
inversions than `w`. It is written out directly rather than through
`upperBruhatLayerLE`, so that no predecessor arithmetic on the bound is needed.
It is not identified with any published layer here.

## Source correspondence

The registered original is `shalika-1974-multiplicity-one`, J. A. Shalika,
*The multiplicity one theorem for GLn*, Ann. of Math. (2) 100 (1974), 171–193.
The retained file is
`/home/taskhub/central-library/Shalika--The multiplicity one theorem for GLn--1974.pdf`,
SHA256 `788c5d124024c768aa47c4e8b179475fbcf5b0882a518ae60b19cdc88089f087`.
Printed pp.174, 175, 178 and 179 are one-based PDF pages 5, 6, 9 and 10. They
were read for this statement, and printed p.175 was checked visually. No
source-specific errata file was found in the project literature index, the
project notes or the Library notes on 2026-10-28.

On printed p.174 Shalika calls the double cosets of `G = GL_n` with respect to
`HU` simply double cosets. Here `H` is the diagonal subgroup and `U` the upper
unipotent subgroup, so `HU` is the upper triangular subgroup. The double cosets
are `G_w = HUwU` for `w` in a fixed system of representatives of the Weyl group
in `N(H)`. Two monomial representatives of the same Weyl element differ by a
diagonal factor in `HU`, so they give the same double coset. As `w` ranges over
all permutations, `permutation n K w` ranges over representatives of every Weyl
element. Since the proposition quantifies over all `w`, the direction of the
permutation convention does not affect the correspondence.

Lemma 1.7 on printed p.175 assumes that `k` is a local field and fixes `w`. Its
part (2) is printed as "Each double coset in the closure of `G_w\G` has
dimension strictly smaller than `G_w`." This statement reads the printed
`G_w\G` as the boundary, the closure of `G_w` with `G_w` itself removed. Read
literally, the set difference `G_w \ G` is empty, and `G_w` itself does not
have strictly smaller dimension than `G_w`. The proof says that (2) is a simple
consequence of the closed orbit lemma, applied to the double cosets of
`G_k̄` with respect to `H_k̄ U_k̄` over the separable algebraic closure `k̄`,
together with `H_k̄ U_k̄ w U_k̄ ∩ G_k = HUwU`. Here "dimension" is the
dimension of the analytic manifold `G_w`, which part (1) provides. The
Corollary on the same page defines `Ω_w` as the union of `G_w` with the double
cosets of strictly larger dimension and asserts that it is open. On printed
pp.178–179 the proof of Theorem 1.6 runs an induction over the unions `ω_j` of
double cosets of dimension at most `r_j`, using Lemma 1.16.

## Internal numerical generalization

The present proposition is an internal derived target, not a verbatim source
theorem. It differs from Lemma 1.7(2) in two ways.

1. The analytic dimension of a double coset is replaced by the inversion count
   of its permutation. The motivation is the parametrization in the proof of
   Lemma 1.7, by `HU × U_w⁻` with `U_w⁻ = U ∩ w⁻¹ Ū w` (printed p.174). The
   project's `permutationUnipotentMinus n K w` is this subgroup with `w`
   represented by `permutation n K w`. In the project's
   conventions the published entry criterion
   `mem_permutationUnipotentMinus_iff_entries` leaves free exactly the entries
   `(i,j)` with `i < j` and `w j < w i`, the pairs counted by
   `permutationInversionCount n w`. So over a local field the dimension of
   `G_w` is expected to be that of `HU` plus the inversion count. This module
   proves no dimension formula, and it does not prove that the analytic
   dimension is an increasing function of the inversion count. Hence it also
   does not prove that the proposition is equivalent to Lemma 1.7(2) over local
   fields.
2. The quantification over all Hausdorff topological fields is the project's
   generalization. Shalika states and proves Lemma 1.7 for local fields only;
   no claim is made that the original treats any wider class of fields. A local
   field whose topology carries these instances is a special case; for example
   Mathlib supplies them for the normed fields `ℝ`, `ℂ` and `ℚ_[p]`.

The general formulation is suggested by finite rank conditions, recorded here
as an indicated route only. On a cell, the ranks of the lower-left submatrices
(rows at least `i`, columns at most `j`) are constant. In a Hausdorff
topological field, an upper bound on such a rank is a closed condition on the
invertible matrices, because it is the vanishing of finitely many minors. A
proof along these lines also needs Bruhat coverage, for which the Library
already has `fieldUpperBruhatFactorizationTheorem` in
`Langlands.Group.GL.UpperBruhatProof`, and a combinatorial comparison between
rank bounds and inversion counts. This module proves none of these steps, and
a later proof may use any other genuine argument.

## What the proposition does not assert or assume

The proposition is a containment with a strict inequality. It does not assert:

- that the boundary equals the union of all cells with fewer inversions, or that
  every such cell meets the closure of `C_w`;
- any closure-order or Bruhat-order characterization of the cells;
- any analytic manifold, submanifold or intrinsic dimension statement, or
  Lemma 1.7(1);
- that `C_w` is locally closed, or that any layer is closed or any
  `upperBruhatCellNeighborhood` is open (Shalika's Corollary);
- disjointness of the cells, coordinate or homeomorphism properties of
  `upperBruhatCellMap` or `upperBruhatTorusMap`, or the factorization
  `U = U_w⁺ U_w⁻` used in the proof of Lemma 1.9 on printed p.176;
- stability of an individual cell under any transpose, `θ`, or Weyl-conjugated
  transpose.

No premise of the proposition assumes a boundary theorem, a rank
characterization, a dimension certificate, local closedness, a coordinate
theorem, a finite-orbit ordering, local compactness, sigma compactness or
countability. In particular the orbit-ordering results in
`Langlands.Representation.Geometric` are neither used nor presumed.

## Status

The proposition is stated and unproved. It is a common geometry prerequisite
for the Shalika distribution and Whittaker multiplicity-one developments; it
is not a proof of either parent theorem.
