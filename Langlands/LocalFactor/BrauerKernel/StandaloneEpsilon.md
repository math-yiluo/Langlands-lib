# Tate epsilon products of standalone Brauer relations

Author: Worker 5093. This is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. In Deligne's global
argument (1973, proof of Lemma 4.12) a global Brauer relation is restricted to every finite place
`z` other than the distinguished one. There it becomes a relation among induced characters of
completions `E_j` of global fields, which are standalone p-adic fields rather than intermediate
fields of the common closure. This unit shows that the product of the corresponding Tate epsilon
ratios is `1`. It reads the published kernel lemmas of `BrauerKernel.StandaloneBridge` as
statements about Tate's local constants on the fields `E_j` themselves.

Everything is in `Langlands.LocalFactor.NonabelianBrauer`. Fix a prime `p`, a p-adic field
`F : PadicField.{u} p`, a reciprocity family `e : ReciprocityFamily F` with
`NormalizedReciprocity F e`, a finite index type `J`, p-adic fields `E j : PadicField.{u} p` in
the universe of `F`, and `ℚ_p`-embeddings `g j : F →ₐ[ℚ_p] E j`. Every p-adic field carries its
canonical topology and the Borel σ-algebra (local instances). For a nontrivial additive character
`ψF` of `F`, `SystemEpsilon.standaloneTraceCharacter F (E j) (g j) ψF` is `ψF ∘ Tr_{E_j/F}`. Write
`ε_j(χ) = PadicAbelian.epsilon (E j).canonicalTopologicalData χ (ψF ∘ Tr_{E_j/F}) μ_j 0` for Tate's
local constant on `E j` at `s = 0` and a Haar measure `μ_j` on `E j`.

## Definition

- `standaloneEpsilonMeasures F : HaarFamily F`: a chosen Haar measure on every finite
  intermediate field of the common closure, from the published
  `CommonClosureSpectralAnalytic.haarMeasure_nonempty`. It is an auxiliary choice. The results
  below do not depend on it.

## Results

- `prod_epsilon_ratio_eq_one_of_evaluationMap`: let `η j`, `η' j` be quasicharacters of `E j`,
  `n : J → ℤ`, `ψ` the bottom-field character of `ψF` (`IsBaseCharacter F ψF ψ`) and `measures` a
  Haar family. If the evaluation map `evaluationMap F (baseExtension F) ψ measures` vanishes on
  `Σ_j n_j · [standaloneGenerator F e (E j) (g j) (η j) (η' j)]`, then for all Haar measures
  `μ_j` on `E j`,

  `Π_j (ε_j(η j) / ε_j(η' j)) ^ n_j = 1`.

  Proof: the published `evaluationMap_imageGenerator` writes the evaluation as
  `Σ_j n_j · generatorValue(...)` in `Additive ℂˣ`. Its vanishing is the product identity
  `Π_j generatorValue(...)^{n_j} = 1` in `ℂˣ`. The published `generatorValue_standaloneGenerator`
  replaces each generator value by `ε_j(η j) / ε_j(η' j)`.
- `prod_epsilon_ratio_eq_one_of_unramified` (**unramified places**): suppose every `E j / F` is
  unramified (equal ramification indices), and there is a quasicharacter `α` of `F` with
  `η j = η₀_j · (α ∘ N_{E_j/F})` and `η' j = η₀'_j · (α ∘ N_{E_j/F})` for unramified `η₀_j`,
  `η₀'_j`. If

  `Σ_j n_j · Ind_{E_j/F}([η j ∘ rec_j] - [η' j ∘ rec_j]) = 0`

  in the continuous Grothendieck group of the Weil group of `F`, then for every nontrivial
  additive character `ψF` of `F` and all Haar measures `μ_j`,
  `Π_j (ε_j(η j) / ε_j(η' j)) ^ n_j = 1`. Here `rec_j` is the transported reciprocity candidate
  `extensionReciprocityCandidate F (E j) (g j) e`, the induction is along
  `extensionWeilMap F (E j) (g j)`, and the norm is taken for the `F`-algebra structure given by
  `g j`. Proof: the published `evaluationMap_standalone_eq_zero_of_unramified` gives the
  vanishing of the evaluation, for the bottom-field character
  `baseFieldAdditiveCharacterEquiv F ψF` (a base character by
  `isBaseCharacter_iff_eq_baseFieldAdditiveCharacterEquiv`) and the measures
  `standaloneEpsilonMeasures F`. Then apply the first result.
- `exists_bound_prod_epsilon_ratio_eq_one_of_ramified` (**ramified places**): for every nontrivial
  `ψF` and every `K : ℕ` there is `B` such that for every quasicharacter `α` of `F` with conductor
  `a(α) ≥ B` the following holds. If `η j = η₀_j · (α ∘ N_{E_j/F})` and
  `η' j = η₀'_j · (α ∘ N_{E_j/F})` with `a(η₀_j), a(η₀'_j) ≤ K`, and the induced relation above
  holds, then `Π_j (ε_j(η j) / ε_j(η' j)) ^ n_j = 1` for all Haar measures `μ_j`. Proof: the
  bound `B` is the one of the published
  `exists_bound_evaluationMap_standalone_eq_zero_of_ramified` for the same bottom-field character
  and measures. Then apply the first result.

## Provenance

These are internal reformulations of the published kernel lemmas of
`BrauerKernel.StandaloneBridge` (Worker 1838). The mathematics is Deligne, *Les constantes des
équations fonctionnelles des fonctions L* (1973): Lemma 4.15 for unramified data and Lemma 4.16
(twists by a highly ramified character) for the ramified bound (printed pages 545–547, PDF pages
45–47), used in the proof of Lemma 4.12 (printed page 544, PDF page 44). Only the form of the conclusion is new: it is stated as an
identity of Tate's local constants on the standalone fields, which is the form needed when the
places of a global field are compared.
