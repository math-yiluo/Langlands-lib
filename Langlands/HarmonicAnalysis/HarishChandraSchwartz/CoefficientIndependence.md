# Independence of coefficient spaces (Waldspurger, VIII.5, proof of Theorem VIII.1.2)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.CoefficientIndependence`,
namespace `Langlands.HarishChandraSchwartz`. It imports and uses:

- `HarishChandraSchwartz.Basic`: `IsBiInvariant`;
- `Representation.IsotypicRestriction`: `Langlands.CompactSplitting.isotypicComponent_eq_iSup_range`
  (the isotypic component of a simple type `S` is the supremum of the ranges of all module maps
  out of `S`);
- `Plancherel.CoefficientTensors`: `coefficientTensorMap`, `range_coefficientTensorMap`;
- `Smooth.Contragredient.CompactDualityProof`: `smoothDualFixedRestriction_bijective`; through
  it `SmoothDual`, `smoothContragredient`, `smoothDualFixedRestriction`, `fixedVectors`;
- `MatrixCoefficient.Definitions`: `matrixCoefficient` (`matrixCoefficient ρ ℓ v g = ℓ (ρ g v)`);
- `Whittaker.Algebraic`: `Whittaker.rightTranslation ℂ G`, right translation
  `(s · f)(g) = f(g s)` on all functions `G → ℂ`;
- `Category.Basic`: `SmoothRep`, `SmoothRep.IsIrreducible`;
- Mathlib: `isotypicComponent`, `sSupIndep_isotypicComponents`,
  `LinearEquiv.isotypicComponent_eq`, `isIsotypicOfType_submodule_iff`,
  `IsIsotypicOfType.isotypicComponent`, `Submodule.le_isotypicComponent`,
  `Representation.irreducible_iff_isSimpleModule_asModule`,
  `Representation.IntertwiningMap.equivLinearMapAsModule`,
  `Representation.IntertwiningMap.ofBijective`, `Subrepresentation.ofSubmodule'`,
  `iSupIndep.linearIndependent`, `LinearIndependent.finite`,
  `Module.Projective.exists_dual_ne_zero`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus
234.

- I.6, printed p. 249 (PDF p. 15): "pour toute représentation admissible `π` de `G`, notons
  `A(π)` le sous-espace de `C_lisse(G)` engendré par les coefficients de `π`."
- VIII.4, printed p. 327 (PDF p. 93): "Pour tout sous-groupe ouvert compact `H` de `G`, posons
  `°C_H = °C(G) ∩ C_H`"; Proposition VIII.4.1: "l'espace `p_χ(°C_H)` est de dimension finie."
- Theorem VIII.1.2, printed p. 321 (PDF p. 87): "Pour tout sous-groupe ouvert compact `H` de
  `G`, `Θ^H_G` est fini."
- VIII.5, printed pp. 331–332 (PDF pp. 97–98), proof of Theorem VIII.1.2. For `χ ∈ Â^H_G`,
  "notons `E₂(G)^H_χ` l'ensemble des `(ω, E) ∈ E₂(G)_χ` tels que l'espace des invariants `E^H`
  soit non nul." After reducing to the finiteness of `E₂(G)^H_χ` for fixed `χ`: "Mais, d'après
  le Théorème VIII.4.2, et puisque `p_χ` est `G × G`-invariante, on a
  `⊕_{ω ∈ E₂(G)^H_χ} A(ω)^{H×H} ⊂ p_χ(°C_H)`, où l'exposant `H×H` désigne les invariants par
  `H×H`. Pour tout `ω ∈ E₂(G)^H_χ`, `A(ω)^{H×H} ≠ {0}`. Comme `p_χ(°C_H)` est de dimension
  finie (Proposition VIII.4.1), `E₂(G)^H_χ` est fini."

This module proves the representation-theoretic steps of the last quotation: the sum of the
coefficient spaces of pairwise inequivalent irreducible representations is direct, each
`A(ω)^{H×H}` is nonzero when `E^H ≠ 0`, and an independent family of nonzero subspaces of a
finite-dimensional space is finite.

## Scope: abstract data and explicit hypotheses

`G` is a topological group (`[Group G] [TopologicalSpace G] [IsTopologicalGroup G]`; the
results marked `omit [IsTopologicalGroup G]` do not use the last instance). Representations are
smooth complex representations `SmoothRep ℂ G` on vector spaces without topology. The module
does not construct `E₂(G)`, `E₂(G)^H_χ`, `°C_H`, `p_χ` or `Θ^H_G`; it does not prove the
inclusion `⊕ A(ω)^{H×H} ⊂ p_χ(°C_H)` (Theorem VIII.4.2), the finite dimension of `p_χ(°C_H)`
(Proposition VIII.4.1), or the reduction from `Θ^H_G` to the sets `E₂(G)^H_χ`. These enter
the final theorem only as the finite-dimensional space `F` and the hypothesis `hF`. The
hypotheses of each result:

- `iSupIndep_isotypicComponent`: a ring `R`, an `R`-module `M`, a family `S : ι → Type*` of
  simple `R`-modules (`[∀ i, IsSimpleModule R (S i)]`) and
  `hS : ∀ i j, Nonempty (S i ≃ₗ[R] S j) → i = j` (pairwise non-isomorphic).
- `iSupIndep_toSubmodule_ofSubmodule'`: a commutative ring `k`, a monoid `H`, a representation
  `ρ : Representation k H W`, a family `N` of `k[H]`-submodules of `ρ.asModule` and
  `hN : iSupIndep N`.
- `coefficientIntertwiningMap ρ ℓ`: `ρ : Representation ℂ G V` and `ℓ : Module.Dual ℂ V` (any
  linear functional).
- `coefficientFunctionSpace A`, `coefficientFunctionSpace_eq_map`: `A : SmoothRep ℂ G`.
- `matrixCoefficient_mem_coefficientFunctionSpace`: `A`, a smooth functional
  `ℓ : SmoothDual A.representation` and a vector `x : A`.
- `iSupIndep_coefficientFunctionSpace`: a family `ω : ι → SmoothRep ℂ G`,
  `hirr : ∀ i, (ω i).IsIrreducible` and
  `hω : ∀ i j, Nonempty ((ω i).representation.Equiv (ω j).representation) → i = j`
  (pairwise inequivalent).
- `exists_isBiInvariant_coefficient_ne_zero`: `A`, an open subgroup `H : OpenSubgroup G`,
  `hH : IsCompact (H : Set G)` and `hfix : fixedVectors A.representation H.toSubgroup ≠ ⊥`
  (`E^H ≠ 0`).
- `finite_of_iSupIndep_of_le`: a field `K`, a `K`-module `E`, a family `B` of submodules,
  `hB : iSupIndep B`, `hne : ∀ i, B i ≠ ⊥`, a submodule `F` with `[FiniteDimensional K F]`
  and `hle : ∀ i, B i ≤ F`.
- `finite_of_isBiInvariant_coefficient_mem`: `ω`, `hirr`, `hω`, `H`, `hH`,
  `hfix : ∀ i, fixedVectors (ω i).representation H.toSubgroup ≠ ⊥`, a submodule
  `F : Submodule ℂ (G → ℂ)` with `[FiniteDimensional ℂ F]`, and
  `hF : ∀ i, ∀ f ∈ coefficientFunctionSpace (ω i), IsBiInvariant H.toSubgroup f → f ∈ F`.

In Waldspurger's situation `ω` runs over representatives of `E₂(G)^H_χ` (irreducible, pairwise
inequivalent, `E^H ≠ 0`), `F = p_χ(°C_H)` and `hF` is the inclusion quoted above.
Square integrability and the central character `χ` are not used by these steps.

## Definitions

- `coefficientIntertwiningMap ρ ℓ`: the linear map `x ↦ (g ↦ ℓ(ρ(g) x))`
  (`matrixCoefficient ρ ℓ`) as an intertwiner from `ρ` to right translation
  `Whittaker.rightTranslation ℂ G` on `G → ℂ`.
- `coefficientFunctionSpace A`: Waldspurger's `A(π)` for `π = A`, the subspace
  `⨆ ℓ : SmoothDual A.representation, LinearMap.range (matrixCoefficient A.representation ℓ)`
  of `G → ℂ`, i.e. the span of the coefficients `g ↦ ℓ(A(g) x)` with `x` a vector and `ℓ` a
  smooth functional. Waldspurger defines `A(π)` for admissible `π` inside `C_lisse(G)`; here
  it is defined for every smooth `A` inside all functions `G → ℂ`, and
  `coefficientFunctionSpace_eq_map` identifies it with the image of the Library's space of
  locally constant coefficients.

## Results

- `iSupIndep_isotypicComponent`: for pairwise non-isomorphic simple modules `S i`, the isotypic
  components `isotypicComponent R M (S i)` of any module `M` are independent.
- `iSupIndep_toSubmodule_ofSubmodule'`: independence of `k[H]`-submodules of `ρ.asModule`
  passes to the underlying `k`-submodules of `W` (`Subrepresentation.ofSubmodule'`).
- `matrixCoefficient_mem_coefficientFunctionSpace`: each coefficient `g ↦ ℓ(A(g) x)` lies in
  `A(A)`.
- `coefficientFunctionSpace_eq_map`: `A(A)` is the image under `LocallyConstant.coeFnₗ ℂ` of
  `LinearMap.range (coefficientTensorMap A)`.
- `iSupIndep_coefficientFunctionSpace` (**the sum `⊕ A(ω)` is direct**): for pairwise
  inequivalent irreducible smooth `ω i`, the spaces `A(ω i)` are independent in `G → ℂ`.
- `exists_isBiInvariant_coefficient_ne_zero` (**`A(ω)^{H×H} ≠ {0}`**): if `A` has a nonzero
  vector fixed by the compact open subgroup `H`, then `A(A)` contains a nonzero function `f`
  with `f(h₁ g h₂) = f(g)` for `h₁, h₂ ∈ H` (`IsBiInvariant H.toSubgroup f`).
- `finite_of_iSupIndep_of_le`: an independent family of nonzero subspaces of one
  finite-dimensional subspace is finite.
- `finite_of_isBiInvariant_coefficient_mem` (**finiteness step of Theorem VIII.1.2**): under
  `hirr`, `hω`, `hH`, `hfix` and `hF`, the index type `ι` is finite.

## Proof notes

1. `iSupIndep_isotypicComponent`: a nonzero component `isotypicComponent R M (S i)` contains a
   submodule `m ≃ S i`, so it equals the isotypic component of the simple submodule `m` and
   belongs to Mathlib's `isotypicComponents R M`, which is `sSupIndep`
   (`sSupIndep_isotypicComponents`). For `j ≠ i` with nonzero component, that component is
   another element of `isotypicComponents R M`; it differs from the `i`-th one, because a
   simple submodule of type `S j` inside the `S i`-isotypic component is isomorphic to `S i`
   (`isIsotypicOfType_submodule_iff`), contradicting `hS`. Zero components are trivial.
2. `iSupIndep_coefficientFunctionSpace`: view right translation on `G → ℂ` as a
   `ℂ[G]`-module. The modules `(ω i).representation.asModule` are simple
   (`irreducible_iff_isSimpleModule_asModule`) and pairwise non-isomorphic (a module
   isomorphism gives an equivalence of representations, contradicting `hω`). Each coefficient
   map `coefficientIntertwiningMap` is a module map out of `(ω i).asModule`, so its range lies in
   the `ω i`-isotypic component (`isotypicComponent_eq_iSup_range`). Step 1 and
   `iSupIndep_toSubmodule_ofSubmodule'` give independence of the components as subspaces of
   `G → ℂ`, and `iSupIndep.mono` restricts it to the `A(ω i)`.
3. `exists_isBiInvariant_coefficient_ne_zero`: take `0 ≠ x ∈ A^H` and a linear functional
   `φ` on `A^H` with `φ x ≠ 0` (`Module.Projective.exists_dual_ne_zero`). Restriction of
   `H`-fixed smooth functionals to `A^H` is bijective (`smoothDualFixedRestriction_bijective`),
   so `φ` is the restriction of an `H`-fixed smooth functional `ℓ`. Then
   `f(g) = ℓ(A(g) x)` satisfies `f(h₁ g h₂) = f(g)` (`x` fixed on the right, `ℓ` fixed on the
   left) and `f(1) = φ x ≠ 0`.
4. `finite_of_iSupIndep_of_le`: choosing a nonzero vector in each `B i` gives a linearly
   independent family (`iSupIndep.linearIndependent`) in the finite-dimensional `F`, so the
   index type is finite.
5. `finite_of_isBiInvariant_coefficient_mem`: apply step 4 to `B i = A(ω i) ⊓ F`, independent
   by step 2 and nonzero by step 3 and `hF`.

The implemented route follows Waldspurger's argument; it takes independence of the `A(ω)`
from the isotypic decomposition of right translation, which Waldspurger leaves implicit in
the notation `⊕`.

## Relation to the Library

- `range_coefficientTensorMap` (`CoefficientTensors`) identifies `LinearMap.range
  (coefficientTensorMap A)` with the span of the smooth matrix coefficients of `A` as locally
  constant functions; `coefficientFunctionSpace_eq_map` relates that form of `A(π)` to the one
  used here.
- `finiteDimensional_of_kernelAlphaChi` (`KernelQuotient`, Proposition VIII.4.1) proves finite
  dimension of a reproducing-kernel space for abstract data; producing `F = p_χ(°C_H)` and `hF`
  for Waldspurger's `G` is not done here.
- `Langlands.CompactSplitting.isotypicPart` and `Langlands.CompactCoefficientClass.isotypicSubrepresentation`
  treat isotypic parts for compact-coefficient classes; they are not used here.

## Open obligations

The construction of `E₂(G)^H_χ`, `°C_H` and `p_χ`, the inclusion
`A(ω)^{H×H} ⊂ p_χ(°C_H)` for `ω ∈ E₂(G)^H_χ` (from Theorem VIII.4.2 and the `G × G`-invariance
of `p_χ`), the finite dimension of `p_χ(°C_H)` for Waldspurger's `G`, and the reduction of
Theorem VIII.1.2 to the finiteness of `E₂(G)^H_χ` (finiteness of `Â^H_G / Im X(G)` and
surjectivity onto `Θ^H_G`) are not proved here.
