# Fitting decomposition of an admissible representation (proof of Corollary III.7.2)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.AdmissibleFitting`,
namespace `Langlands.HarishChandraSchwartz`. It imports
`Langlands.Representation.Compact.ProjectionProof` (`Compact.averageMap`,
`Compact.averageMap_mem_fixedVectors`, `Compact.averageMap_id`,
`Compact.averageMap_commute`), `Langlands.Representation.Smooth.FixedVectors.Definitions`
(`fixedVectors`, `fixedVectorsMap`), `Langlands.Representation.Smooth.FixedVectors.OrderProof`
(`fixedVectors_antitone`), and from Mathlib `Mathlib.RepresentationTheory.Subrepresentation`
(`Subrepresentation`) and `Mathlib.RingTheory.Artinian.Module`
(`LinearMap.eventually_iSup_ker_pow_eq`, `LinearMap.eventually_iInf_range_pow_eq`,
`LinearMap.isCompl_iSup_ker_pow_iInf_range_pow`: the Fitting decomposition of an
endomorphism of a finite-dimensional space). `IsSmooth` and `IsAdmissible` come from
`Langlands.Representation.Smooth.Definitions`, imported through the fixed-vector modules.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus
234.

- Corollary III.7.2 (printed p. 275, PDF p. 41): "Soient `ω ∈ E_2(G)` et `(π, V)` une
  représentation admissible tempérée de `G`. Alors il existe une unique décomposition en
  somme directe: `(π, V) = (π_1, V_1) ⊕ (π_2, V_2)` telle que (i) tous les sous-quotients
  irréductibles de `π_1` sont isomorphes à `ω`; (ii) aucun sous-quotient irréductible de
  `π_2` n'est isomorphe à `ω`."
- Proof of Corollary III.7.2 (printed pp. 275–276, PDF pp. 41–42): with `π(p)` the operator
  of Proposition III.7.1 for a suitable polynomial `p`, "Posons `V_1 = ⋂_{n∈ℕ} π(p)^n V`,
  `V_2 = ⋃_{n∈ℕ} Ker π(p)^n`. Ces sous-espaces sont invariants par `G`. Soit `H` un
  sous-groupe ouvert compact de `G`. Comme `V^H` est de dimension finie, il existe `n(H)` tel
  que pour tout `n ≥ n(H)`, `π(p)^n V^H = π(p)^{n(H)} V^H`,
  `(Ker π(p)^n) ∩ V^H = (Ker π(p)^{n(H)}) ∩ V^H`. (3) On en déduit aisément
  `π(p)^n V^H ∩ (Ker π(p)^n) = {0}` (4) si `n ≥ n(H)`, puis, par comparaison des dimensions,
  toujours pour `n ≥ n(H)`: `V^H = π(p)^n V^H ⊕ ((Ker π(p)^n) ∩ V^H) = V_1^H ⊕ V_2^H`. En
  faisant varier `H`, on obtient `V = V_1 ⊕ V_2`. On déduit de (3) et (4) que l'opérateur
  `π_1(p)` est bijectif tandis que `π_2(p)` est nilpotent."

This passage uses only that `π` is admissible and that `π(p)` commutes with `G`. This
module formalizes it for an arbitrary intertwiner `T : V → V` in place of `π(p)`; the
temperedness of `π` and the choice of `p` are not used here.

Derived statements not displayed in the source: `mem_iSup_ker_pow`,
`intertwiningMap_pow_apply`, `fixedVectorsMap_pow_apply`, `mapsTo_fittingRange`,
`mapsTo_fittingKernel`, `exists_fixed_preimage_pow`, `exists_isCompact_fixed` and
`mem_iInf_range_fixedVectorsMap_pow` are the elementary steps behind "Ces sous-espaces sont
invariants par `G`", "on en déduit aisément" and "en faisant varier `H`". The source's
"`π_2(p)` est nilpotent" is formalized as `exists_pow_eq_zero_of_mem_fittingKernel`: on
`V_2 ∩ V^K` a single power of `T` is zero, for each open subgroup `K` (the power depends on
`K`).

## Scope: abstract data and explicit hypotheses

`G` is a group, `ρ : Representation ℂ G V` is a representation on a complex vector space
`V`, and `T : ρ.IntertwiningMap ρ` is an arbitrary intertwiner. `IsAdmissible ρ` is the
Library's notion: `ρ` is smooth and `V^K` is finite-dimensional for every open subgroup `K`
(Casselman's all-open-subgroups convention). The hypotheses of each result are:

- `mem_iSup_ker_pow`: an endomorphism `f` of a complex vector space; no other hypothesis.
- `intertwiningMap_pow_apply`, `fittingRange`, `mem_fittingRange_iff`, `fittingKernel`,
  `mem_fittingKernel_iff`, `mapsTo_fittingRange`, `mapsTo_fittingKernel`: none beyond `T`.
- `fixedVectorsMap_pow_apply`: a subgroup `K` of `G`.
- `exists_pow_eq_zero_of_mem_fittingKernel`: `[TopologicalSpace G]`,
  `hρ : IsAdmissible ρ` and an open subgroup `K`.
- `exists_fixed_preimage_pow`: `[TopologicalSpace G]`, `[IsTopologicalGroup G]`,
  `hρ : IsSmooth ρ`, an open subgroup `K` with `hK : IsCompact (K : Set G)`, and
  `x ∈ V^K` with `x ∈ Tⁿ V`.
- `exists_isCompact_fixed`: `[TopologicalSpace G]`, `hρ : IsSmooth ρ`, and
  `hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K`
  (every open subgroup contains a compact open subgroup; for a p-adic group this holds
  because the compact open subgroups form a neighbourhood basis of `1`, which is not proved
  here).
- `mem_iInf_range_fixedVectorsMap_pow`: `[TopologicalSpace G]`, `[IsTopologicalGroup G]`,
  `hρ : IsSmooth ρ`, an open subgroup `K` with `hK : IsCompact (K : Set G)`, and
  `x ∈ V_1 ∩ V^K`.
- `isCompl_fittingRange_fittingKernel`, `bijOn_fittingRange`: `[TopologicalSpace G]`,
  `[IsTopologicalGroup G]`, `hρ : IsAdmissible ρ` and `hcof` as above.

## Definitions

- `fittingRange T : Subrepresentation ρ` is `V_1 = ⋂_{n∈ℕ} Tⁿ V`, the infimum of the ranges
  `LinearMap.range (T.toLinearMap ^ n)`, with the proof that it is `G`-stable.
- `fittingKernel T : Subrepresentation ρ` is `V_2 = ⋃_{n∈ℕ} Ker Tⁿ`, the supremum of the
  kernels `LinearMap.ker (T.toLinearMap ^ n)` (an increasing union, so the supremum is the
  union, `mem_fittingKernel_iff`), with the proof that it is `G`-stable.

## Results

- `mem_iSup_ker_pow`: `v ∈ ⨆ n, Ker fⁿ ↔ ∃ n, fⁿ v = 0`.
- `intertwiningMap_pow_apply`: `Tⁿ (ρ(g) v) = ρ(g) (Tⁿ v)`.
- `fixedVectorsMap_pow_apply`: the `n`-th power of the restriction
  `fixedVectorsMap T K : V^K → V^K` is the restriction of `Tⁿ`.
- `mem_fittingRange_iff`: `v ∈ V_1 ↔ ∀ n, v ∈ Tⁿ V`; `mem_fittingKernel_iff`:
  `v ∈ V_2 ↔ ∃ n, Tⁿ v = 0`.
- `mapsTo_fittingRange`, `mapsTo_fittingKernel`: `T` maps `V_1` into `V_1` and `V_2` into
  `V_2`.
- `exists_pow_eq_zero_of_mem_fittingKernel`: for admissible `ρ` and an open subgroup `K`,
  there is `n` with `Tⁿ v = 0` for every `v ∈ V_2 ∩ V^K`.
- `exists_fixed_preimage_pow`: if `x ∈ V^K ∩ Tⁿ V` with `K` compact open, then `x = Tⁿ y`
  for some `y ∈ V^K`.
- `exists_isCompact_fixed`: under `hcof`, every vector of a smooth representation is fixed
  by a compact open subgroup.
- `mem_iInf_range_fixedVectorsMap_pow`: for `K` compact open, a vector of `V_1 ∩ V^K` lies
  in `⋂_n (T|_{V^K})ⁿ V^K`.
- `isCompl_fittingRange_fittingKernel`: `V = V_1 ⊕ V_2`, i.e. the underlying submodules of
  `fittingRange T` and `fittingKernel T` are complementary (`IsCompl`).
- `bijOn_fittingRange`: `T` is a bijection of `V_1` onto itself (`Set.BijOn`), the source's
  "`π_1(p)` est bijectif".

## Proof notes

- `fittingRange`, `fittingKernel`: `G`-stability follows from `intertwiningMap_pow_apply`:
  if `v = Tⁿ y` then `ρ(g) v = Tⁿ (ρ(g) y)`, and if `Tⁿ v = 0` then `Tⁿ (ρ(g) v) = 0`.
- `exists_pow_eq_zero_of_mem_fittingKernel`: `V^K` is finite-dimensional, so the kernels of
  the powers of `T|_{V^K}` stabilize at some `N` (`LinearMap.eventually_iSup_ker_pow_eq`,
  the source's (3)); a vector of `V_2 ∩ V^K` lies in `⨆ₙ Ker (T|_{V^K})ⁿ = Ker (T|_{V^K})^N`.
- `exists_fixed_preimage_pow`: the averaging projection `Compact.averageMap` onto `V^K`
  commutes with `T` (`Compact.averageMap_commute`) and fixes `x`, so
  `x = e_K (Tⁿ y) = Tⁿ (e_K y)`.
- `isCompl_fittingRange_fittingKernel`: given `x`, choose a compact open `K` fixing `x`
  (`exists_isCompact_fixed`) and apply Mathlib's Fitting decomposition
  `LinearMap.isCompl_iSup_ker_pow_iInf_range_pow` to `T|_{V^K}` on the finite-dimensional
  `V^K` (the source's (3), (4) and comparison of dimensions). Disjointness: a vector of
  `V_1 ∩ V_2` fixed by `K` lies in `⋂ₙ (T|_{V^K})ⁿ V^K` (`mem_iInf_range_fixedVectorsMap_pow`)
  and in `⨆ₙ Ker (T|_{V^K})ⁿ`, so it is `0`. Codisjointness: the decomposition of `x` in
  `V^K` gives a component in `⋂ₙ (T|_{V^K})ⁿ V^K ⊆ V_1` and one in
  `⨆ₙ Ker (T|_{V^K})ⁿ ⊆ V_2`.
- `bijOn_fittingRange`: injectivity because `x - y ∈ V_1 ∩ Ker T ⊆ V_1 ∩ V_2 = 0`.
  Surjectivity: for `x ∈ V_1` fixed by a compact open `K`, the ranges of the powers of
  `T|_{V^K}` stabilize at some `N` (`LinearMap.eventually_iInf_range_pow_eq`); writing
  `x = (T|_{V^K})^{N+1} c`, the vector `(T|_{V^K})^N c` lies in
  `⋂ₙ (T|_{V^K})ⁿ V^K ⊆ V_1` and `T` maps it to `x`.

## Relation to the Library

The Library's `Langlands.Representation.SubrepresentationLattice` provides the lattice
structure on `Subrepresentation`; it is not needed here, since the decomposition is stated
for the underlying submodules. `Langlands.Representation.Jacquet.CompressionStabilizationStatement`
and its proof apply the same Mathlib Fitting lemma to the compressed action
`Langlands.Jacquet.compressedAction ρ hρ K hK g` on the single finite-dimensional space
`V^K`; that operator is not an intertwiner and the result does not concern subspaces of `V`.
No earlier Library module decomposes an admissible representation along an intertwiner; the
module reuses the Library's averaging projection `Compact.averageMap` and Mathlib's
finite-dimensional Fitting lemma.

## Open obligations

Not formalized here:

- The operator `π(p)` of Proposition III.7.1 (see `SchwartzActionFamily` for the first half
  of its construction), the finiteness of the set `Σ` of elements of the orbit `O`
  occurring as subquotients of `π`, and the choice of the polynomial `p`.
- The action of `π_1(p)`, `π_2(p)` on irreducible subquotients (by a nonzero scalar,
  resp. by `0`), and hence properties (i) and (ii) of Corollary III.7.2 and the uniqueness
  of the decomposition. Corollary III.7.2 itself remains open.
