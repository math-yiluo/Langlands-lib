# Vanishing from open restrictions along the finite upper Bruhat filtration

Authors: Worker 1082 and Worker 634. The proposition follows Worker 634's
design: the hypotheses of the theorem `vanishing` in that worker's private
draft `BruhatFiltrationVanishingCore` (shared parent draft revision 8 of
task `f79ca82c-d050-4ffa-821b-c347b60e36e0`).

`Langlands.HarmonicAnalysis.Distribution.BruhatFiltrationVanishingStatement.{u}`
is a `Prop`-valued definition in the module
`Langlands.HarmonicAnalysis.Distribution.BruhatFiltrationVanishingStatement`.
This module only states the proposition. It does not prove it, and no
published theorem proves it yet (see [Status](#status)).

## Exact proposition

Inside the namespace `Langlands.HarmonicAnalysis.Distribution`, with
`open GeneralLinear` (that is, `Langlands.GeneralLinear`), the proposition is

```text
∀ (n : ℕ) (K : Type u) [Field K] [TopologicalSpace K]
  [IsTopologicalDivisionRing K] [T2Space K]
  [LocallyCompactSpace (GeneralLinear n K)]
  [TotallyDisconnectedSpace (GeneralLinear n K)]
  (D : Distribution (GeneralLinear n K)),
  (∀ w : Equiv.Perm (Fin n),
    D ∈ supportedOn (upperBruhatLayerLE n K (permutationInversionCount n w)) →
      restrictOpen (isOpen_upperBruhatCellNeighborhood w) D = 0) →
  D = 0
```

In words: let `n` be a natural number and `K` a field in universe `u`. Give
`K` a Hausdorff topology that makes it a topological division ring. Assume
that `GL_n(K)`, with its actual topology, is locally compact and totally
disconnected. Let `D` be a complex algebraic distribution on `GL_n(K)`.
Suppose that for every permutation `w` of `{0, …, n-1}` the following
implication holds:

> if `D` is supported on the union of the upper Bruhat cells with at most
> `ℓ(w)` inversions, then the restriction of `D` to the open neighborhood
> `Ω_w` of the cell `C_w` is zero.

Then `D = 0`. Here `ℓ(w)` is the inversion count of `w`, and `Ω_w` is the
union of `C_w` and all cells with strictly more inversions than `w`.

## Quantifiers and hypotheses

All quantifiers are inside the proposition.

- The rank `n : ℕ` is arbitrary, including `n = 0`.
- `K : Type u` is any field in the single universe `u`. Its topology is
  arbitrary subject to two conditions. `IsTopologicalDivisionRing K` asks for
  continuous addition, negation and multiplication, and continuous inversion
  away from zero. `T2Space K` asks for the Hausdorff property. There is no
  hypothesis that `K` is local, nonarchimedean, locally compact or
  second countable, and no hypothesis on the characteristic or a valuation.
- `LocallyCompactSpace (GeneralLinear n K)` and
  `TotallyDisconnectedSpace (GeneralLinear n K)` are instance hypotheses about
  the existing topology of the group (described below). They are not new
  topologies. When they fail for a given `K` and `n`, the proposition says
  nothing about that `K` and `n`. For a nonarchimedean local field both hold.
- `D` is an arbitrary element of `Distribution (GeneralLinear n K)`.
- The single premise on `D` is quantified over every permutation
  `w : Equiv.Perm (Fin n)`. For each `w` it is an implication. Its antecedent
  is support of the same `D` on the layer at the inversion count of `w`. Its
  consequent is that the actual open restriction of `D` to the cell
  neighborhood of `w` is zero.
- The conclusion is `D = 0` in the full algebraic dual.

The proposition assumes none of the following: an initial support bound on
`D`; equivariance under a unipotent subgroup or a Whittaker character;
bi-equivariance; transpose stability or anti-invariance; invariance under any
group action. It does not replace the actual cells by finitely many unipotent
orbits, does not use a surrogate for open restriction, and does not take any
vanishing of `D` itself as a premise. The premise only concludes something
about `D` when `D` is already supported on the relevant layer.

## Exact meaning of the imported objects

**The group and its topology.** `Langlands.GeneralLinear n K` is Mathlib's
`Matrix.GeneralLinearGroup (Fin n) K`, the units of the matrix ring. It
carries the existing units topology, induced by `g ↦ (g, op g⁻¹)` into the
product of the matrix space with its opposite; the matrix space has the
entrywise product topology. The Hausdorff instance needed by `restrictOpen`
is inferred from `T2Space K` (Mathlib's `Units.instT2Space`). Every subset of
the group, such as `Ω_w`, has its subspace topology.

**Distributions.** `Distribution X` is the Library's
`Module.Dual ℂ (SchwartzBruhat X)`. These are all complex linear functionals
on the complex-valued, locally constant, compactly supported functions on `X`.
No continuity condition is imposed.

**Support convention.** For any subset `Z`, not necessarily closed,
`supportedOn Z` is the submodule of distributions `D` such that `D f = 0` for
every test function `f` that vanishes at every point of `Z`
(`Distribution.mem_supportedOn_iff`). The layers used here are closed (see
below), but closedness is not part of the proposition.

**Open restriction.** For an open `U` in a Hausdorff space,
`restrictOpen hU D` is the distribution on the subspace `U` given by
`f ↦ D (SchwartzBruhat.extendZero hU f)`. Here `extendZero hU f` is the test
function on `X` that equals `f` on `U` and is zero outside `U`
(`Distribution.restrictOpen_apply`). So `restrictOpen hU D = 0` means `D`
vanishes on every test function that is the zero extension of a test function
on `U`.

**Cells, inversion counts and layers.** These are the published definitions in
`Langlands.Group.GL.UpperBruhatCells` and
`Langlands.Group.GL.UpperBruhatFiltration`.

- `upperBruhatCell n K w` is the set of `b₁ * permutation n K w * b₂` with
  `b₁` and `b₂` in the upper triangular subgroup `upperTriangularSubgroup n K`.
  The matrix `permutation n K w` is Mathlib's permutation matrix of `w⁻¹`.
- `permutationInversionCount n w` is the number of ordered pairs `(i, j)` in
  `Fin n` with `i < j` and `w j < w i`.
- `upperBruhatLayerLE n K k` is the union of the cells `upperBruhatCell n K v`
  over the permutations `v` with `permutationInversionCount n v ≤ k`.
- `upperBruhatCellNeighborhood n K w` is the union of `upperBruhatCell n K w`
  and the set `upperBruhatHigherCells n K w` of matrices lying in a cell
  `upperBruhatCell n K v` with
  `permutationInversionCount n w < permutationInversionCount n v`.

**The openness proof.** `isOpen_upperBruhatCellNeighborhood w` is the
published theorem `Langlands.GeneralLinear.isOpen_upperBruhatCellNeighborhood`
in `Langlands.Group.GL.UpperBruhatFiltrationGeometryProof`. For a Hausdorff
topological division ring `K` it proves that
`upperBruhatCellNeighborhood n K w` is open. The proposition uses it only as
the openness argument of `restrictOpen`. The same module proves that every
layer `upperBruhatLayerLE n K k` is closed (`isClosed_upperBruhatLayerLE`) and
that every invertible matrix lies in exactly one cell
(`exists_mem_upperBruhatCell`, `upperBruhatCell_index_eq`).

**Rank zero.** For `n = 0` the group has one element, the only permutation
is `1`, its inversion count is `0`, and its cell, layer and neighborhood are
the whole group. The premise for `w = 1` then gives `D = 0` once one observes
that every distribution is supported on the whole group and that restriction
to the whole group loses no test function.

## Provenance

This is an internal derived interface. It was built from the published actual
Bruhat partition and inversion-layer topology
(`Langlands.Group.GL.UpperBruhatFiltrationGeometryProof`) and the published
Schwartz–Bruhat subspace maps (`Langlands.HarmonicAnalysis.Distribution.Subspace`).
It is not a verbatim transcription of a theorem in the literature.

The finite support-removal pattern matches the argument of Shalika (1974),
*The multiplicity one theorem for GLn*, Ann. of Math. 100, 171–193
(`shalika-1974-multiplicity-one`), printed pp.178–179 (PDF pages 9–10).
At the bottom of printed p.178, Shalika lists the dimensions
`r_0 = -1 < r_1 < ⋯ < r_N` of the double cosets, including the empty set.
`ω_j` is the union of the double cosets of dimension `≤ r_j`, and
`Λ_w = Λ | Ω_w` is the restriction of a distribution `Λ` to `Ω_w`. The proof
of Lemma 1.16 (printed p.179) describes `Ω_w` as the union of `G_w` with the
double cosets of dimension `> r_j`, where `dim G_w = r_j`, and uses that
`Ω_w` is open. Lemma 1.16 says that if `Λ` has support in `ω_j`, then `Λ_w`
has support in `G_w`. The proof of Theorem 1.6 (printed p.179) applies
Proposition 1.17 to get `Λ_w = 0`. So no point of `G_w` lies in `Supp Λ`,
hence `Supp Λ ⊂ ω_{j-1}`, and induction finishes the proof. Proposition 1.14
(printed p.178) is the corresponding locality step for a closed support set:
it is proved with neighborhoods of zero restriction and the localization
lemma.

The present proposition differs from that source in these ways.

- It indexes the filtration by the numerical inversion count of the actual
  cells `B · permutation w · B`, where Shalika uses the dimension of the
  double coset. No identification of the two orderings is used or claimed.
- It isolates only the support-removal step. Shalika derives the vanishing
  of each restriction `Λ_w` from Proposition 1.17, using equivariance of `Λ`
  under left and right translation by `U` with the character `χ` and its
  anti-invariance `Λ(f) = -Λ(f^θ)`. Here that vanishing is an abstract
  premise on `D`, required only when `D` is supported on the corresponding
  layer.
- It is stated for every Hausdorff topological field such that `GL_n(K)` is
  locally compact and totally disconnected, and for full algebraic duals, not
  only for distributions on `GL_n` of a nonarchimedean local field.

## Intended proof (not established here)

This module does not prove the proposition. The intended later proof is a
finite induction on the layers. It uses a generic locality criterion for
algebraic distributions on a Hausdorff, locally compact, totally disconnected
space: if every point outside `Z` has an open neighborhood on which the open
restriction of `D` is zero, then `D` is supported on `Z`. That criterion is
the subject of the separate statement task
`8f638667-3516-41d7-8f57-f33c0dcaf304`. It is neither imported nor assumed
here.

1. *Initial layer.* Every invertible matrix lies in some actual cell, and
   every inversion count is at most `n * n`. So the layer at `n * n` is the
   whole group, and every `D` is supported on it.
2. *Removing the top count.* Suppose `D` is supported on the layer at `k`.
   The layer is closed, and the restriction of `D` to its open complement is
   zero, directly from the support condition and extension by zero. Let `g` be
   a point of the layer outside the union of the cells with fewer than `k`
   inversions. Then `g` lies in a cell `C_w` with exactly `k` inversions. The
   premise for this `w` applies, because `D` is supported on the layer at
   `ℓ(w) = k`. So the restriction of `D` to the open set `Ω_w`, which contains
   `g`, is zero. Locality then puts `D` on the union of the cells with fewer
   than `k` inversions, which is the layer at `k - 1` when `k ≥ 1` and the
   empty set when `k = 0`.
3. *Conclusion.* After finitely many steps `D` is supported on the empty set.
   Every test function vanishes on the empty set, so `D = 0`.

The route uses no decomposition into finitely many unipotent orbits and no
symmetry of `D`. A private Lean implementation of this route exists in the
shared draft `BruhatFiltrationVanishingCore` cited above, but it has not been
reviewed or published. It depends on a private locality proof, so it gives
no public theorem.

## Status

Only the statement is published here. Its proof is a separate later task.
It is expected to import the generic open-restriction locality theorem once
that theorem's statement and proof are independently published.
