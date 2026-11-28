# Two-sided translates and maximal compact right averages of adelic test functions

Module `Langlands.Global.AdelicTestFunctionCompactAverage`, namespace
`Langlands.Global.AdelicGroupPoints`.

Let `F` be a number field and `G` an affine group scheme over `Spec F`. An adelic test function
(`IsAdelicTestFunction F G h`, module `Langlands.Global.AdelicLocalFinitenessStatement`) is a
continuous function on `G(𝔸)` whose infinite slices `x ↦ h(x, b)` are plot-smooth, which is right
invariant under an open subgroup of `G(𝔸_f)`, has compact support and is left invariant under an
open subgroup of `G(𝔸_f)`. Write `G(𝔸) = G(F_∞) × G(𝔸_f)` with the inclusions `ofInfinite`,
`ofFinite` and projections `infinite`, `finite` (module `Langlands.Global.AdelicGroupProduct`).

## Translates and sums

- `isAdelicTestFunction_comp_mul_mul`: for a smooth structure `hsmooth` and `g₁, g₂ ∈ G(𝔸)`,
  `x ↦ h(g₁ x g₂)` is an adelic test function when `h` is. The infinite slice at `b` is the slice
  of `h` at `g₁,f b g₂,f` composed with `x ↦ g₁,∞ x g₂,∞`, smooth by `isPlotSmooth_iff_contMDiff`
  and smoothness of multiplication on the Lie group `G(F_∞)`. The right and left levels are the
  conjugates of those of `h` by `finite g₂` and `finite g₁` (`finite_conjugation`).
- `isAdelicTestFunction_add`, `isAdelicTestFunction_zero`, `isAdelicTestFunction_finset_sum`:
  sums and finite sums of adelic test functions are adelic test functions (levels are
  intersections of the levels).

## Right averages over a maximal compact subgroup

- `maximalCompactRightAverage K hK a h z = ∫_K a(k) h(z k) dk`, for a compact subgroup `K` of
  `G(𝔸)`, a weight `a` on `K` and the Haar probability measure `compactHaarProbability F G K hK`.
- `isAdelicTestFunction_maximalCompactRightAverage`: let `G` be locally of finite type with a
  smooth structure, `K` a maximal compact subgroup of `G(𝔸)` (`IsMaximalCompactSubgroup`), `a`
  continuous on `K` and right invariant under `ofFinite(L₀)` for an open subgroup `L₀` of `G(𝔸_f)`
  (whenever `k · ofFinite(l)` lies in `K`). Then the right average of an adelic test function `h`
  with weight `a` is an adelic test function. The proof writes `K = K_∞ × K_f`
  (`IsMaximalCompactSubgroup.mem_iff`), partitions `K` by the finitely many cosets of the compact
  group `K_f` modulo the open subgroup `(L₀ ∩ L₁) ∩ K_f` (`L₁` a right level of `h`;
  `Subgroup.quotient_finite_of_isOpen`), and on the coset of a representative `r` rewrites
  `a(k) h(z k)` as `a(k_∞ r) h(z k_∞ r)`. Each piece is the Library's right average over the
  compact subgroup `K_∞` of `G(F_∞)` (`rightCompactKernelAverage`, with the image measure of the
  restricted Haar measure of `K` and a continuous weight) of the right translate `y ↦ h(y r)`. It
  is a test function by `isAdelicTestFunction_rightCompactKernelAverage` and the translate result
  above.

## Right finiteness under a maximal compact subgroup

`exists_maximalCompact_rightTranslate_decomposition`: let `K` be a maximal compact subgroup of
`G(𝔸)` and `φ` a continuous function on `G(𝔸)` whose right translates by
`K_∞ = K.comap ofInfinite` span a finite-dimensional space (`IsInfiniteSubgroupFiniteFunction`)
and which is right invariant under `ofFinite(L)` for an open subgroup `L` of `G(𝔸_f)`. Then there
are `k₁, …, k_n ∈ K` and continuous functions `a_j` on `K`, right invariant under `ofFinite(L)`,
with `φ(z k) = ∑_j a_j(k) φ(z k_j)` for all `k ∈ K` and `z ∈ G(𝔸)`.

The span `V` of the right `K`-translates lies in the finite sum, over the finitely many cosets
`r (L ∩ K_f)` of `K_f`, of the images of the span of the `K_∞`-translates under right
translation by `r`, so it is finite-dimensional. A linearly independent subfamily of the
translates spanning `V` (`exists_linearIndependent`) is a basis. The coefficients are the basis
coordinates of `z ↦ φ(z k)`. They are continuous in `k`, because `k ↦ (z ↦ φ(z k))` is continuous
for the topology of pointwise convergence and linear functionals on a finite-dimensional
Hausdorff topological vector space are continuous.

## Provenance

This is an internal development. It supplies the reductions of compact Iwasawa integrals to
finitely many test functions used in the Riesz representation of the norm-one Levi pairings of
Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series* (2024), §6.2, (6.8),
p. 202.
