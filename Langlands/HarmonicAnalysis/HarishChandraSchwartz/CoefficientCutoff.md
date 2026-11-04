# Coefficients cut off by `C_c(G/G¹)` lie in `C(G)` (III.7)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.CoefficientCutoff`,
namespace `Langlands.HarishChandraSchwartz`. It imports `Translations`
(`TranslationWeights`, with fields `pos`, `nonneg`, `bound`, `heightBound`), through it
`Basic` (`nu`, `weight`, `IsBiInvariant`, `IsBiInvariant.mono`, `levelSubmodule`,
`schwartzSubmodule`, `levelSubmodule_le_schwartzSubmodule`, `CompactOpenSubgroup`), and
`Langlands.Representation.Plancherel.CoefficientTensors` (`SmoothRep`, `CoefficientTensor`,
`coefficientTensorMap`, `coefficientTensorAction`, `coefficientTensorMap_tmul`,
`coefficientTensorMap_action`, `coefficientTensorMap_biInvariant`).

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus
234.

- III.7 (printed p. 273, PDF p. 39), second paragraph: "Soient `(ω, E)` une représentation
  admissible de carré intégrable de `G`, `f ∈ A(ω)` et `ϕ ∈ C_c(G/G¹)`. Il résulte du
  Corollaire III.1.2 que la fonction produit `fϕ` appartient à `C(G)`."
- Corollary III.1.2 (printed p. 263, PDF p. 29): "Supposons `π` de carré intégrable. Alors
  pour tout `f ∈ A(π)` et tout `r ∈ ℝ`, il existe `c > 0` tel que pour tout `g ∈ G¹`, on ait
  l'inégalité `|f(g)| ⩽ cΞ(g)(1 + σ(g))^{-r}`." Its proof (printed p. 264) begins "On peut
  supposer `f` de la forme `f(g) = ⟨π(g)v, v̌⟩` pour des éléments `v ∈ V`, `v̌ ∈ V̌`."
- I.6 (printed p. 249, PDF p. 15): "pour toute représentation admissible `π` de `G`, notons
  `A(π)` le sous-espace de `C_lisse(G)` engendré par les coefficients de `π`."
- I.1 (printed p. 239, PDF p. 5): `G¹ = ⋂_{χ ∈ Rat(G)} Ker |χ|_F`.
- III.6 (printed p. 271, PDF p. 37): "`ν_r(f) = sup{|f(g)|Ξ(g)^{-1}(1 + σ(g))^r; g ∈ G}`.
  Pour tout sous-groupe ouvert compact `H` de `G`, on note `C_H` l'espace des
  `f ∈ C(H \ G/H)` telles que `ν_r(f)` soit fini pour tout `r ∈ ℝ`. [...] On pose
  `C(G) = ⋃_H C_H`, où `H` parcourt l'ensemble des sous-groupes ouverts compacts de `G`."
  (formalized in `Basic` as `levelSubmodule` and `schwartzSubmodule`).

Waldspurger gives no further argument. The proof below supplies it: the bounds of
Corollary III.1.2 on `G¹` are transported to each coset `g₀ G¹` (via the left translates
`f(g₀ ·)`, again in `A(ω)`) with Lemma II.1.2 and the translation bound for `σ`, and `ϕ` is
supported on finitely many cosets.

## Scope: abstract data and explicit hypotheses

The group `G` is a topological group; in the main results it has a compact open subgroup
(`[Nonempty (CompactOpenSubgroup G)]`). The weights `Ξ, σ : G → ℝ` are arbitrary. Nothing is
proved here about Waldspurger's own `Ξ`, `σ` or `G¹`.

- `G¹` is replaced by an arbitrary subgroup `N` with `[N.Normal]` and `hN : IsOpen (N : Set G)`.
  Waldspurger's `G¹` is open and normal; this is not proved here. The published
  `Plancherel.commonNormKernel` (`Langlands.Representation.Plancherel.UnramifiedCharacters`)
  is the intersection of the kernels of a family of characters; its docstring describes `G¹` as
  the rational-character specialization.
- `ϕ ∈ C_c(G/G¹)` is a function `φ : G ⧸ N → ℂ` with `HasCompactSupport φ`, for the quotient
  topology. Since `N` is open, `G ⧸ N` is discrete, so every function on it is continuous and
  `HasCompactSupport φ` means that `φ` has finite support. The product `fϕ` is the function
  `g ↦ f(g) φ(gN)`.
- `C(G)` is `schwartzSubmodule Ξ σ` of `Basic`.
- The representation is a smooth representation `A : SmoothRep ℂ G` (published category of
  smooth representations, carrier `A`, action `A.representation`). `A(π)` is
  `LinearMap.range (coefficientTensorMap A)`: the image of the coefficient map
  `A ⊗ Ã → LocallyConstant G ℂ`, `v ⊗ ℓ ↦ (g ↦ ℓ(π(g) v))`, with `Ã` the smooth dual. The
  published `range_coefficientTensorMap` identifies it with the span of the coefficients,
  as in I.6. Admissibility, a unitary central character and square integrability of `ω` are not
  hypotheses: they enter the source argument only through Corollary III.1.2, whose conclusion
  is the hypothesis `hD`.
- Corollary III.1.2 is not formalized. Its conclusion for the pure coefficients is the
  hypothesis `hD : HasRapidlyDecreasingCoefficientsOn Ξ σ N A.representation`: for all
  `v ∈ A`, smooth functionals `ℓ` and `r ∈ ℝ` there is a real `c` with
  `|ℓ(π(n) v)| ≤ c Ξ(n)(1 + σ(n))^{-r}` for all `n ∈ N`. The source asks for `c > 0`; a real
  `c` is a weaker requirement, so Corollary III.1.2 implies `hD` (for `N = G¹`).
- The weights satisfy `ht : TranslationWeights Ξ σ` of `Translations`: `Ξ > 0`, `σ ≥ 0`,
  Lemma II.1.2 for `Ξ` (`TranslationBound`) and the translation bound
  `1 + σ(g₁ g g₂) ≤ C (1 + σ(g))` for `σ` (`HeightTranslationBound`).

The hypotheses of each result are:

- `IsRapidlyDecreasingOn.add`: none beyond `[Group G]`.
- `nu_ne_top_of_norm_le`: `hΞ : ∀ g, 0 < Ξ g`, `hσ : ∀ g, 0 ≤ σ g`, and a bound
  `h : ∀ g, ‖f g‖ ≤ c * Ξ g * (1 + σ g) ^ (-r)` on all of `G`.
- `TranslationWeights.exists_norm_le_of_mem_coset`: `ht : TranslationWeights Ξ σ`, a subgroup
  `N`, `g₀ : G`, and `hf : IsRapidlyDecreasingOn Ξ σ N (fun x => f (g₀ * x))`.
- `IsBiInvariant.mul_quotient`: subgroups `H ≤ N` (`hHN`) with `[N.Normal]`, and
  `hf : IsBiInvariant H f`; `φ : G ⧸ N → ℂ` arbitrary.
- `TranslationWeights.mul_mem_levelSubmodule`: `[TopologicalSpace G] [IsTopologicalGroup G]`,
  `ht`, `[N.Normal]`, `hN : IsOpen (N : Set G)`, a subgroup `H` with `hHN : H ≤ N`,
  `hf : IsBiInvariant H f`, `hdec : ∀ g₀, IsRapidlyDecreasingOn Ξ σ N (fun x => f (g₀ * x))`,
  and `hφ : HasCompactSupport φ`.
- `isRapidlyDecreasingOn_coefficientTensorMap` and
  `isRapidlyDecreasingOn_coefficientTensorMap_mul_left`: `[IsTopologicalGroup G]`, `hD`.
- `TranslationWeights.coefficientTensorMap_mul_mem_schwartzSubmodule` and
  `TranslationWeights.mul_mem_schwartzSubmodule`: `[IsTopologicalGroup G]`,
  `[Nonempty (CompactOpenSubgroup G)]`, `ht`, `[N.Normal]`, `hN`, `hD`, and
  `hφ : HasCompactSupport φ`; the second also `hf : f ∈ LinearMap.range (coefficientTensorMap A)`
  for `f : LocallyConstant G ℂ`.

## Definitions

- `IsRapidlyDecreasingOn Ξ σ N f`: for every `r : ℝ` there is `c : ℝ` with
  `‖f n‖ ≤ c * Ξ n * (1 + σ n) ^ (-r)` for all `n ∈ N` (the bound of Corollary III.1.2).
- `HasRapidlyDecreasingCoefficientsOn Ξ σ N ρ`, for `ρ : Representation ℂ G V`: every
  coefficient `g ↦ ℓ.val (ρ g v)`, `v : V`, `ℓ : SmoothDual ρ`, satisfies
  `IsRapidlyDecreasingOn Ξ σ N` (the conclusion of Corollary III.1.2 for pure coefficients).

## Results

- `IsRapidlyDecreasingOn.add`: rapid decay on `N` is stable under sums.
- `nu_ne_top_of_norm_le`: a bound `‖f g‖ ≤ c Ξ(g)(1 + σ(g))^{-r}` on `G` gives `ν_r(f) ≠ ∞`.
- `TranslationWeights.exists_norm_le_of_mem_coset`: if `f(g₀ ·)` decreases rapidly on `N`,
  then for every `r` there is `c` with `‖f g‖ ≤ c Ξ(g)(1 + σ(g))^{-r}` for all `g` with
  `g₀⁻¹ g ∈ N`, i.e. on the coset `g₀ N`, with the weights evaluated at `g` itself.
- `IsBiInvariant.mul_quotient`: if `f` is `H`-bi-invariant and `H ≤ N`, then
  `g ↦ f(g) φ(gN)` is `H`-bi-invariant.
- `TranslationWeights.mul_mem_levelSubmodule`: under the hypotheses above,
  `(fun g => f g * φ g) ∈ levelSubmodule Ξ σ H`; for a compact open `H` this is
  Waldspurger's `C_H`.
- `isRapidlyDecreasingOn_coefficientTensorMap`: under `hD`, every `coefficientTensorMap A t`,
  `t : CoefficientTensor A`, decreases rapidly on `N`.
- `isRapidlyDecreasingOn_coefficientTensorMap_mul_left`: under `hD`, so does every left
  translate `x ↦ coefficientTensorMap A t (g₀ * x)`.
- `TranslationWeights.coefficientTensorMap_mul_mem_schwartzSubmodule`: for every
  `t : CoefficientTensor A`, `(fun g => coefficientTensorMap A t g * φ g) ∈ schwartzSubmodule Ξ σ`.
- `TranslationWeights.mul_mem_schwartzSubmodule` (III.7): for every
  `f ∈ LinearMap.range (coefficientTensorMap A)`, `(fun g => f g * φ g) ∈ schwartzSubmodule Ξ σ`.

## Proof notes

`exists_norm_le_of_mem_coset`: put `n = g₀⁻¹ g ∈ N`, so `g = g₀ n`. Lemma II.1.2
(`ht.bound`, with exponent `d`, applied with `g₁ = g₀⁻¹`, `g₂ = 1`) gives
`Ξ(n) ≤ C₁ Ξ(g)(1 + σ(g))^d`, and the height bound (`ht.heightBound g₀ 1`) gives
`1 + σ(g) ≤ C₂ (1 + σ(n))`. With `s = max(r, 0) + d ≥ 0` and the bound
`|f(g₀ n)| ≤ c Ξ(n)(1 + σ(n))^{-s}` from the hypothesis, this yields
`|f(g)| ≤ c C₁ C₂^s Ξ(g)(1 + σ(g))^{d - s} ≤ c C₁ C₂^s Ξ(g)(1 + σ(g))^{-r}`. The constants
are nonnegative, which is read off from the inequalities at `g = 1`.

`mul_mem_levelSubmodule`: bi-invariance is `IsBiInvariant.mul_quotient` (normality of `N`
handles the left factor). Since `N` is open, `G ⧸ N` is discrete
(`QuotientGroup.discreteTopology`), so the compact support of `φ` is finite. For each coset `q`
choose the constant `c_q` of `exists_norm_le_of_mem_coset` at the representative
`Quotient.out q`. Then `‖f(g) φ(gN)‖ ≤ (∑_q |c_q| ‖φ(q)‖) Ξ(g)(1 + σ(g))^{-r}` for all `g`, the
sum running over the support of `φ`, and `nu_ne_top_of_norm_le` gives `ν_r < ∞`.

`isRapidlyDecreasingOn_coefficientTensorMap` is tensor induction (`TensorProduct.inductionOn`):
pure tensors are `hD` (by `coefficientTensorMap_tmul`), sums are
`IsRapidlyDecreasingOn.add`. The left translate of `coefficientTensorMap A t` by `g₀` is
`coefficientTensorMap A (coefficientTensorAction A (1, g₀⁻¹) t)` by
`coefficientTensorMap_action`, so it is again rapidly decreasing; this is the stability of
`A(ω)` under left translation used implicitly in the source.

For `coefficientTensorMap_mul_mem_schwartzSubmodule`, `coefficientTensorMap_biInvariant` gives
an open subgroup `U` under which the coefficient is bi-invariant. The intersection
`H = K₀ ∩ U ∩ N` of a compact open subgroup `K₀` with `U` and `N` is a compact open subgroup
contained in `N`, `mul_mem_levelSubmodule` puts the product in `C_H`, and
`levelSubmodule_le_schwartzSubmodule` puts it in `C(G)`. `mul_mem_schwartzSubmodule` is the
same statement for `f` in the range of the coefficient map.

## Relation to the Library

`Plancherel.range_coefficientTensorMap` (`Langlands.Representation.Plancherel.CoefficientTensors`)
identifies `A(π)` as used here with the span of the smooth matrix coefficients, and
`coefficientTensorMap_biInvariant` (built on `matrixCoefficient_biInvariant`) provides the
bi-invariance. `enorm_centralProjection_le_rpow_neg` (module `CentralProjection`) proves bounds of the same
shape `|f(g)| ≤ c Ξ(g)(1 + σ(g))^{-r}` on a set `S` (for Waldspurger `S = G¹`) for the central
projections of VIII.4.1, a different statement.

## Open obligations

Corollary III.1.2 itself (which rests on Proposition III.1.1, cited by Waldspurger from
Casselman's notes) is not formalized, nor are the facts that Waldspurger's `G¹` is open and
normal and that his `Ξ`, `σ` satisfy `TranslationWeights`. Proposition III.7.1 (the operators
`π(p)`) is not covered.
