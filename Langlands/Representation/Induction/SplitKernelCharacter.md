# Character-twisted relative integration over a split kernel

Author: Worker 837.

This pair extends the published split-kernel relative integral from the trivial
character to an arbitrary smooth character `θ` of the kernel. If `θ` is trivial
on `I = H ∩ N`, the pair identifies the actual `θ`-localized quotient of compact
induction from `H` with the ordinary coinvariants of the restricted inducing
representation of `I`. The entry declaration is
`Langlands.Induction.splitKernelCharacterEquiv`. The `θ`-twisted section
covariance is `Langlands.Induction.splitKernelCharacterIntegral_section`.

The pair is an internal prerequisite of the boundary clause
`MirabolicProductMinus.RightPhiBoundary`, which is proved in
`Langlands.Representation.Derivative.MirabolicProductMinusRightBoundary`.

## Provenance

The pair is derived and internal. It states no external theorem. Its results
are compositions of published Library constructions:

- `compactInductionTwistEquiv` (Induction/CharacterTwistProof), the
  character-twist identification of compact induction;
- `compactInducedMap`, `compactInduced`, `eval` and `CompactFunctions`
  (Induction/Definitions);
- `splitKernelCompactEquiv` with `_translate`, `_natural` and
  `_section_eval` (Induction/SplitKernelCompact), the restriction of
  compactly induced functions to the kernel `N`;
- `splitKernelCompactIntegral`, `isClosed_splitKernelIntersection`,
  `isSmooth_splitKernelInducing` and `splitKernelInducingMap`
  (Induction/SplitKernelIntegral);
- `splitKernelCompactIntegral_section`, `splitKernelConjugation`,
  `splitKernelConjugation_mem` and `splitKernelCoefficientAction`
  (Induction/SplitKernelCovariance);
- `compactCoinvariantIntegral` with `_translate` and `_natural`, and
  `compactCoinvariantDesc` (Induction/CompactCoinvariantIntegral);
- `compactCoinvariantIntegralBijective`
  (Induction/CompactCoinvariantBijectivityProof), the published bijectivity of
  the coinvariant integral;
- `Jacquet.Localization.relations`, `mk`, `lift` and their lemmas
  (Jacquet/Localization).

In BZ77 (Bernstein–Zelevinsky, *Induced representations of reductive p-adic
groups I*, Ann. Sci. ENS (4) 10 (1977), source ID
`bernstein-zelevinsky-1977-induced-i`), the corresponding step is the orbit
computation of Theorem 5.2 in the proof of 4.13(b,c) (§7.2, printed p.471).
That proof leaves the details to the reader. This pair proves only the general
single-orbit identity used below, with an arbitrary character `θ`. No Haar
scaling, comparison or invariance premise is added beyond the explicit
hypotheses listed below.

## Setting

`G` is a locally compact topological group and `L` a group with a topology.
`r : G →* L` and `s : L →* G` are continuous homomorphisms with
`r (s l) = l`. `H` is a closed
subgroup of `G` that contains `s L`. Write `N = r.ker`,
`I = H.comap N.subtype` and `σI` for the restriction of a smooth complex
representation `σ` of `H` to `I`. `θ : SmoothCharacter ℂ N` is a smooth
character with `hθ : ∀ i : I, θ i = 1`. `ν` is a measure on the left quotient
`I\N` that is finite on compacts. The universes of `G`, `L`, `N`, `V` and `W`
are independent.

## Multiplication by a character

- `compactFunctions_eval_ext`: compactly induced functions are determined by
  their values. The published `Induction/OpenAdjunction` has the same fact
  under the name `compactFunctions_ext`. This pair does not import that module,
  and the distinct name avoids a clash in modules that import both.
- `inverseCharacter χ` is the pointwise inverse of a smooth character, with the
  same open kernel.
- `twistTrivialIntertwining I χ hχ σ` is the identity map from the twist of `σ`
  by `χ|I` to `σ`. It is an intertwiner because `χ` is trivial on `I`.
- `characterMultiply I χ hχ σ` is the published twist equivalence
  `compactInductionTwistEquiv` followed by `compactInducedMap` of that
  intertwiner. `eval_characterMultiply` states its value
  `x ↦ χ(x) • f(x)` (by `rfl`).
- `characterMultiply_inverse_apply` and `characterMultiply_apply_inverse`: the
  maps for `χ` and `χ⁻¹` are mutually inverse.
- `characterMultiply_translate`: right translation by `n` commutes with the
  multiplication up to the scalar `χ(n)⁻¹`.
- `characterMultiply_natural`: the multiplication commutes with every
  coefficient intertwiner.

## The twisted relative integral

Write `E = splitKernelCompactEquiv …` and `M` for multiplication by `θ⁻¹`.

```text
splitKernelCharacterIntegral f = compactCoinvariantIntegral I σI ν (M (E f)),
```

so the integral is `f ↦ [∫_{I\N} θ(n)⁻¹ f(n) dν]`, with values in
`Representation.Coinvariants σI`.

- `splitKernelCharacterIntegral_eq`: the twisted integral is the published
  untwisted `splitKernelCompactIntegral` of `E⁻¹ (M (E f))`.
- `splitKernelCharacterIntegral_translate`: if `ν` is invariant under right
  translation by `N`, kernel translation by `n` multiplies the integral by
  `θ(n)`. The proof combines the published translation laws of `E` and of
  the coinvariant integral with `characterMultiply_translate`.
- `relations_le_ker_splitKernelCharacterIntegral`: hence every actual
  `θ`-relation `n • f - θ(n) f` lies in the kernel. This uses
  `Jacquet.Localization.relations_le_ker_iff`.
- `coinvariantsKer_le_comap_relations`: in the other direction, `E⁻¹`
  after multiplication by `θ` sends the ordinary coinvariant relations of
  `I`-compact induction into the `θ`-relations.

## Bijectivity

Assume further that `G` is Hausdorff and `N` locally compact. `N` and `I`
carry Borel structures and right-invariant regular Haar measures `μN`, `μI`.
`N` has a basis of compact open subgroups at the identity (`hBasis`), and `ν`
is compatible with `μN`, `μI` (`QuotientIntegration.IsCompatible`).

- `ker_splitKernelCharacterIntegral`: the kernel is exactly
  `Jacquet.Localization.relations (compactInduced H σ) N θ`. Inclusion `⊆`
  applies injectivity from the published `compactCoinvariantIntegralBijective`
  to `M (E f)`. Then `coinvariantsKer_le_comap_relations` and the inverse laws
  bring the element back. Inclusion `⊇` is the previous lemma.
- `splitKernelCharacterIntegral_surjective`: surjectivity comes from the
  published bijectivity and from `characterMultiply_inverse_apply`.
- `splitKernelCharacterEquiv`: the actual linear equivalence

  ```text
  Jacquet.Localization.Coinvariants (compactInduced H σ) N θ
    ≃ₗ[ℂ] Representation.Coinvariants σI
  ```

  is `Jacquet.Localization.lift` of the twisted integral. It is made bijective
  by the two previous results. `splitKernelCharacterEquiv_mk` gives its value
  on classes by `rfl`.

## Naturality and section covariance

- `splitKernelCharacterIntegral_natural`: for an intertwiner `T : σ → τ` of
  smooth representations of `H`, the twisted integral commutes with
  `compactInducedMap H T` and `Coinvariants.map (splitKernelInducingMap r H T)`.
- `splitKernelCharacterIntegral_section`: let `l : L` satisfy
  `θ(α_l n) = θ(n)` for all `n`, where
  `α_l = splitKernelConjugation r s l` is `n ↦ s(l)⁻¹ n s(l)`. Then

  ```text
  ∫θ (s(l) • f) = (Δ_I(α_l) / Δ_N(α_l)) • D(l) (∫θ f),
  ```

  where `Δ` is `mulEquivHaarChar` and `D = splitKernelCoefficientAction`. The
  proof shows that `M (E (s(l) • f)) = E (s(l) • E⁻¹ (M (E f)))`, pointwise.
  This uses `splitKernelCompactEquiv_section_eval` and the `θ`-invariance
  hypothesis. It then applies the published untwisted section law
  `splitKernelCompactIntegral_section` to `E⁻¹ (M (E f))`.

## Imports and dependency audit

Direct imports: `Langlands.Representation.Induction.SplitKernelCovariance`,
`Langlands.Representation.Induction.CharacterTwistProof` and
`Langlands.Representation.Jacquet.Localization`. The project import closure has
73 modules besides this one. All of them are published Library modules, and
they are contained in the closure listed in `MirabolicProductMinusRightBoundary.md`.
No module in the closure is a plus functor or adjunction module, §4.13(d), a
Leibniz or filtration proof, a finiteness or classification consumer, or a
Whittaker finiteness statement. The proofs use only the published theorems
named above and Mathlib. No proposition definition is used as a hypothesis.
Axioms: `propext`, `Classical.choice` and `Quot.sound`.
