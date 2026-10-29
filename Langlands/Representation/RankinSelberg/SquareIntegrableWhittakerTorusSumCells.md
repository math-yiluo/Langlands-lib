# Disjoint cells below the antitone torus cone

Authors: Worker 906; Worker 6 (copied diagonal-entry lemma); Worker 113 (shared diagonal
conjugation lemmas); Worker 819 (cell pattern).

This module is the second helper for the proof of
`Langlands.RankinSelberg.SquareIntegrableWhittakerTorusSumStatement`
(see [`SquareIntegrableWhittakerTorusSumProof`](SquareIntegrableWhittakerTorusSumProof.md)).
It contains internal helper lemmas only; none of them is a published statement.
It proves the standard lower bound: the volume of the double coset `K a K` modulo the centre
is at least a constant times `δ(a)⁻¹`, and a bi-`K`-invariant square-integrable coefficient
therefore has square-summable values on the antitone torus cone. The route below, through an
index count in the upper-unipotent group and explicit disjoint cells, is internal to this
project. The cell argument follows the pattern of `cells_tsum_lt_top` in the published module
`Langlands.Representation.Exponents.ExtractedCoefficientL2ObstructionCells` (author
Worker 819).

Notation: `G = GL_(m+1)(F)`, `Z` its centre, `N = upperUnipotent (m + 1) F`,
`K(r) = Conductor.principalLevelSubgroup F m r`, and `ϖ^lam = Iwasawa.torus ϖ lam`.

## Disjointness modulo the centre

Section `Algebra` works over any field `k` with a valuative relation.

- `upperTriangular_mul_diag` (private): the diagonal of a product of upper-triangular
  matrices is the product of the diagonals. It is copied verbatim from the published module
  `Langlands.Group.GL.UpperUnipotent` (author Worker 6), where it is private.
- `unipotent_torus_unipotent_diag`: for upper-unipotent `u` and `u'`, the `i`-th diagonal
  entry of `u ϖ^lam u'` is `ϖ ^ lam i`.
- `torus_neg`: `(ϖ^lam)⁻¹ = ϖ^(-lam)`.
- `eq_of_mem_center`: let `r > 0` and `ϖ` be uniformizing. Suppose
  `(ϖ^lam h k₁)⁻¹ (ϖ^lam' h' k₂)` is central, where `lam` and `lam'` have the same last
  entry, `h` and `h'` are upper unipotent, and `k₁, k₂ ∈ K(r)`. Then `lam = lam'` and
  `h⁻¹ h' ∈ K(r)`.

  Proof. Put `d = lam' - lam`, `x = h⁻¹ ϖ^d h'` and `e = k₁ k₂⁻¹ ∈ K(r)`. Write the central
  element `z` as the scalar matrix `c`. Then `x = e z`, so `e⁻¹ = x⁻¹ z`. The last diagonal
  entry of `x⁻¹` is `ϖ ^ (-d_last) = 1`, so `c` is the last diagonal entry of `e⁻¹`.
  Hence `c - 1` lies in `𝔪^r`. Then `exists_mem_principalLevelSubgroup` (published module
  `UnequalRankMirabolicUnitTestProof`, author Worker 856) puts `z` in `K(r)`, so
  `x = e z ∈ K(r)`. The diagonal entries `ϖ ^ d_i` of `x` and `ϖ ^ (-d_i)` of `x⁻¹` are
  then integral. Since `0 < v(ϖ) < 1`, this gives `d_i ≥ 0` and `-d_i ≥ 0`, so `d = 0`.
  Finally `x = h⁻¹ h'`.

## Diagonal conjugation on the upper-unipotent group

The declarations `diagonalConj`, `diagonalConj_val`, `continuous_diagonalConj`,
`diagonalConj_map` and `singleton_modulus_real` are imported from
[DiagonalUnipotentHaar](DiagonalUnipotentHaar.md). This shared module contains
Worker 113's unchanged helpers extracted from `QuotientIwasawaIntegrationProof`.

- `diagonalConj a u = diag(a) u diag(a)⁻¹`.
- `diagonalConj_map`: it scales `unipotentHaar` by `δ(a)⁻¹`, where `δ` is the singleton
  Levi modulus `T.leviModulus (singletons (m + 1)) (singletonLevi F a)`.
- `singleton_modulus_real`: `δ(a) = ∏_{i<j} |a_i / a_j|` for the normalized absolute value.

## The index of `N ∩ K(r)` in `H_a`

- `unipotentLevel k m r` is the subgroup `N ∩ K(r)` of `N`.
- `conjLevel m r a` is `H_a = {u ∈ N | diag(a) u diag(a)⁻¹ ∈ K(r)}`; `mem_conjLevel`
  unfolds it.
- `unipotentLevel_le_conjLevel`: if `v(ϖ) ≤ 1` and `lam` is antitone, then
  `N ∩ K(r) ≤ H_a` for `a = (ϖ ^ lam i)_i`. This is `torus_conj_upper_mem` from the
  [`SquareIntegrableWhittakerTorusSumCoefficient`](SquareIntegrableWhittakerTorusSumCoefficient.md)
  module.
- `index_conjLevel`: in that situation `N ∩ K(r)` has finite index in `H_a`, equal to
  `δ(a)⁻¹` (as an extended nonnegative real).

  Proof. Give `N` its Borel structure and `ν = unipotentHaar`. The set `N ∩ K(r)` is open
  and compact, so `0 < ν(N ∩ K(r)) < ∞`. `H_a` is the preimage of `N ∩ K(r)` under
  `diagonalConj a`, so it is open, and it is the image of `N ∩ K(r)` under
  `diagonalConj a⁻¹`, so it is compact. An open subgroup of a compact group has finite
  index (`Subgroup.quotient_finite_of_isOpen`). Mathlib's `Subgroup.index_mul_measure`,
  applied in `H_a` to the left-invariant pullback of `ν`, gives
  `index · ν(N ∩ K(r)) = ν(H_a)`. By `diagonalConj_map`,
  `ν(H_a) = δ(a)⁻¹ ν(N ∩ K(r))`. Cancel `ν(N ∩ K(r))`.

## Cells and square-summability on the antitone cone

`summable_antitone F T m r hr`: let `r > 0` and `ϖ` be uniformizing. Let `π` be a
representation of `G` with unitary central character `c`, `L` a linear functional with
`L (π g w) = L w` for `g ∈ K(r)`, and `v` a vector fixed by `K(r)`. Let `μ` be a Haar
measure on `G / Z` for a Borel measurable structure, and suppose
`c.coefficientNorm L v` is in `L²(μ)`. Then

`(∏_{i<j} |ϖ^(e_i) / ϖ^(e_j)|)⁻¹ ‖L (π(ϖ^e) v)‖²`, with `e = Fin.snoc lam 0`,

is summable over the `lam : Fin m → ℤ` for which `Fin.snoc lam 0` is antitone.

Proof. The cells are indexed by the countable type of pairs `(lam, q)`, with `lam` in
the cone and `q ∈ H_a / (N ∩ K(r))`, each fibre being finite. The cell of `(lam, q)` is the
left translate of the image of `K(r)` in `G / Z` by the image of `ϖ^e h`, where `h`
represents `q`. The cells are open, hence measurable, and each has measure
`μ(image of K(r))` by left invariance. They are pairwise disjoint by `eq_of_mem_center`.
On the cell of `(lam, q)`,

`‖L (π(ϖ^e h k) v)‖ = ‖L (π(ϖ^e h ϖ^(-e)) π(ϖ^e) π(k) v)‖ = ‖L (π(ϖ^e) v)‖`,

because `ϖ^e h ϖ^(-e) ∈ K(r)` and `k ∈ K(r)`. The published `countableCellLpLower` gives a
finite sum. Summing over each finite fibre multiplies by its cardinality, which is
`δ⁻¹` by `index_conjLevel`. The image of `K(r)` is open and nonempty, so it has positive
measure and can be cancelled. Finally the finite sum of nonnegative reals is converted to
real summability, and `singleton_modulus_real` writes `δ` as the product.
