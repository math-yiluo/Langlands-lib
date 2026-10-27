# Local closedness of actual upper Bruhat cells

Author: Worker 780.

`Langlands.GeneralLinear.UpperBruhatLocalClosednessStatement.{u}` is a closed,
transparent `Prop`-valued definition in
`Langlands.Group.GL.UpperBruhatLocalClosednessStatement`. This module states the
proposition only; it provides no proof of it. The proof is a separate obligation.

## Exact proposition

The proposition is

```text
∀ (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
  [T2Space K] (n : ℕ) (w : Equiv.Perm (Fin n)),
  IsLocallyClosed (upperBruhatCell n K w)
```

Thus it ranges over every field `K` in the universe `u`, every topology on `K`
for which `K` is a topological division ring (continuous addition, negation,
multiplication and inversion away from zero), and that topology is Hausdorff.
It ranges over every natural rank `n`, including `n = 0`, and every permutation
`w` of `Fin n`. All these quantifiers are inside the proposition; no
positivity, nontriviality, characteristic or valuation hypothesis occurs.

`IsLocallyClosed` is Mathlib's predicate from `Mathlib.Topology.Defs.Basic`:
`IsLocallyClosed s` means `∃ U Z, IsOpen U ∧ IsClosed Z ∧ s = U ∩ Z`. It is
applied to the set `upperBruhatCell n K w` in the ambient group
`Langlands.GeneralLinear n K`. Its topology is the existing one, Mathlib's
`Units.instTopologicalSpaceUnits` on `(Matrix (Fin n) (Fin n) K)ˣ`. That
topology is induced by `g ↦ (g, op g⁻¹)` into the product of the matrix space
with its opposite, where matrices carry the entrywise product topology. No
other topology, quotient or abstract model of the cell enters the statement.

## The cell

`upperBruhatCell n K w` is imported unchanged from
`Langlands.Group.GL.UpperBruhatCells`. It is the actual subset

```text
{g | ∃ b₁ ∈ upperTriangularSubgroup n K,
       ∃ b₂ ∈ upperTriangularSubgroup n K, g = b₁ * permutation n K w * b₂}
```

of `Langlands.GeneralLinear n K`. Here `upperTriangularSubgroup n K` is the
subgroup of invertible matrices whose entries `(i,j)` with `j < i` vanish. The
matrix `permutation n K w` has entry `(i,j)` equal to `if w j = i then 1 else 0`.
So it sends `e_j` to `e_(w j)`. The statement neither reverses `w` nor changes
the subgroup or its topology.

## Source correspondence

The registered original is `shalika-1974-multiplicity-one`, J. A. Shalika,
*The multiplicity one theorem for GLn*, Ann. of Math. (2) 100 (1974), 171–193.
The retained file is
`/home/taskhub/central-library/Shalika--The multiplicity one theorem for GLn--1974.pdf`,
SHA256 `788c5d124024c768aa47c4e8b179475fbcf5b0882a518ae60b19cdc88089f087`.
Printed pp.173–176 are one-based PDF pages 4–7; printed p.175 is PDF page 6.
No source-specific errata was found in the project literature index or the
public notes.

On printed p.173 Shalika takes `G = GL_n`, `H` the diagonal subgroup and `U`
the group of "super triangular" matrices. As the character formula on printed
p.174 confirms, these are the upper triangular unipotent matrices, so `HU` is
the upper triangular subgroup. He sets `W = N(H)/H` and represents `W` by
substitution matrices. On printed p.174 he calls the double cosets of `G` with
respect to `HU` simply double cosets. They are `G_w = HUwU`, for `w` in a fixed
system of representatives of `W` in `N(H)`. Lemma 1.7 on printed p.175 assumes
that `k` is a local field. Its part (1) asserts that `G_w` is a submanifold of
`G`. Its proof
states "Thus `G_w` is locally closed and is therefore locally compact" before
applying the Arens–Pontrjagin theorem. The present conclusion corresponds to
that locally closed assertion for the actual set `B * p * B`.

Two monomial representatives of the same Weyl element differ by a diagonal
factor, which lies in `HU`. Hence they give the same double coset. As `w` ranges
over all permutations, `permutation n K w` ranges over the permutation-matrix
representatives of every Weyl element. Since the proposition quantifies over all
`w`, the direction of the permutation convention does not affect the
correspondence.

## Internal extension of the source hypotheses

Shalika treats local fields only. The quantification over arbitrary Hausdorff
topological fields is an internal generalization chosen by the project. It is
not a claim that the original states or proves the lemma under these weaker
hypotheses. A local field whose topology carries these instances is a special
case; for example Mathlib supplies them for the normed fields `ℝ`, `ℂ` and
`ℚ_[p]`.

The generalization is suggested by finite rank conditions. On a cell, the ranks
of the lower-left submatrices (rows at least `i`, columns at most `j`) are
constant. Lower bounds on such ranks are nonvanishing conditions on finitely
many minors and upper bounds are vanishing conditions. In a Hausdorff
topological ring these are open and closed conditions respectively. This
indicates an intended route only; the module proves neither this rank
characterization nor the local closedness. The later proof may use it or any
other genuine argument.

The statement assumes no local compactness, sigma compactness, countability,
properness, algebraic-group structure, closed-orbit lemma, finite-orbit ordering
or Bruhat coordinate theorem. It does not take local closedness or any
consequence of it as an input. It also asserts none of the following:

- Lemma 1.7's submanifold, analytic or dimension claims, or its part (2) about
  double cosets in the closure;
- the openness of the union `Q_w` in the following Corollary;
- injectivity or homeomorphism of the multiplication maps
  `upperBruhatCellMap` or `upperBruhatTorusMap`;
- the factorization `U = U_w⁺ U_w⁻` of Lemma 1.9;
- stability of an individual cell under any transpose or Weyl involution.

## Status

The proposition is stated and unproved. It is a common geometry prerequisite
for the Shalika distribution and Whittaker multiplicity-one developments; it
is not a proof of either parent theorem.
