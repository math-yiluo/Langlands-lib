# Regularity thresholds of two root presentations of one parabolic

Module `Langlands.Global.AdelicEisensteinRegularityPresentationComparison` proves
`Langlands.Global.RootPresentationRegularityComparisonStatement` (module
`Langlands.Global.AdelicEisensteinRegularityPresentationComparisonStatement`), as
`Langlands.Global.rootPresentationRegularityComparison`. The proof uses only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Statement

Let `G` be a connected reductive group over a number field `F`. Let `r₁` be a root presentation
of `p₁ : P₁ → G` with Levi `l₁ : M₁ → P₁` and split component `a₁ : A₁ → M₁`, and `r₂` one of
`p₂ : P₂ → G` with `l₂`, `a₂`. Let `e : P₂ → P₁` satisfy `e ≫ p₁ = p₂`, and suppose the two
parabolics have the same image in `G` and the two Levis have the same image. For every real `R`
there is a real `R'` such that every complex parameter `λ` of `P₁` whose restriction along `e`
is `R'`-regular for `r₂` is `R`-regular for `r₁`.

## Helper lemmas

- `parameterRestrict_innerIso_hom`: restriction of complex parameters along an inner
  automorphism `(H.innerIso n).hom` is the identity. On a pure tensor `s ⊗ χ` this is the
  conjugation invariance of rational characters, `rationalCharacters.comp_innerIso_hom`.
- `parameterRestrict_comp_innerIso_hom`: restriction along `e ≫ (H.innerIso n).hom` agrees with
  restriction along `e`. It follows from the previous lemma, because restriction along a
  composite is the composite of the restrictions (`characterRestrict_comp`).

## Proof of `rootPresentationRegularityComparison`

1. **The common Levi.** The Levi maps `l₁ ≫ p₁` and `l₂ ≫ p₂` are closed subgroups with equal
   ranges. `IsClosedSubgroup.sourceIsoOfRangeEq` gives an isomorphism `c : M₂ ≅ M₁` with
   `c ≫ l₁ ≫ p₁ = l₂ ≫ p₂`. `ParabolicRootPresentation.exists_leviTorusLift` lifts the
   presentation tori to maximal split tori `t₁ : T₁ → M₁` and `t₂ : T₂ → M₂` with
   `t_k ≫ l_k ≫ p_k = r_k.data.i`.
2. **Conjugating the tori.** The Levi `M₁` is smooth, affine and connected
   (`IsRationalLeviSubgroup.isConnectedReductive`). `smoothMaximalSplitTorusConjugacy`, applied
   in `M₁` to `t₂ ≫ c` and `t₁`, gives a rational point `z` of `M₁` and an isomorphism
   `φ : T₂ ≅ T₁` with `(t₂ ≫ c) ≫ inner(z) = φ ≫ t₁`. Let `g` be the image of `z` in `G`. Then
   `r₂.data.i ≫ inner(g) = φ ≫ r₁.data.i` in `G`, by `innerIso_hom_comp`.
3. **The conjugated second presentation.** Write `E = G.innerIso g`. Then
   `r₂' = r₂.compAmbientIso E` is a presentation of `p₂ ≫ E` with torus inclusion
   `r₂.data.i ≫ E`. The point `g` lies in the Levi, and so in the parabolic.
   `range_comp_innerIso_of_mem` and `SubgroupFunctor.range_comp_iso_eq_iff` therefore give
   `range (p₂ ≫ E) = range p₁` and `range (l₂ ≫ p₂ ≫ E) = range (l₁ ≫ p₁)`.
4. **A presentation of the first parabolic with the second torus.** Let `ψ : T₁ ≅ T₂` be the
   inverse of `φ` as an isomorphism of commutative group schemes
   (`CommGroupScheme.isoOfGroupIso`). The data `⟨T₂, r₂.data.i ≫ E, ν₂, J₂, r₁.data.f ≫ ψ⟩`
   are compatible with `(p₁, l₁, a₁)`:
   - the parabolic, Levi and split-component fields come from `r₁`;
   - the torus, generic cocharacter, simple roots, minimality and realization fields come from
     `r₂'`, with the ranges rewritten by step 3;
   - the factorization `ψ ∘ r₁.data.f` through `r₂.data.i ≫ E` holds because
     `ψ ≫ r₂.data.i ≫ E = r₁.data.i` (step 2).

   Call this presentation `s`.
5. **Comparison of `r₁` with `s`.** The presentations `r₁` and `s` belong to the same parabolic,
   Levi and split component. Their torus inclusions are identified by `ψ`, and their
   split-component factors correspond under `ψ`. `eisensteinRegularityTorusComparison`
   (module `Langlands.Global.AdelicEisensteinRegularityTorusComparison`) gives, for the given
   `R`, a threshold `S` such that `S`-regularity for `s` implies `R`-regularity for `r₁`. Take
   `R' = S`.
6. **Comparison of `s` with `r₂`.** Let `j = e ≫ inner_{P₁}(z')`, where `z'` is the image of `z`
   in `P₁`. Then `j ≫ p₁ = p₂ ≫ E`, by `innerIso_hom_comp` and `e ≫ p₁ = p₂`. The presentations
   `s` (of `p₁`) and `r₂'` (of `p₂ ≫ E`) share the torus inclusion, the generic cocharacter and
   the simple roots. So `eisensteinRegularityParabolicTransport` (module
   `Langlands.Global.AdelicEisensteinRegularityParabolicTransport`) identifies `S`-regularity of
   `λ` for `s` with `S`-regularity of `parameterRestrict j λ` for `r₂'`. Further,
   `parameterRestrict j λ = parameterRestrict e λ` by `parameterRestrict_comp_innerIso_hom`.
   Finally, `eisensteinRegularityAmbientTransport` identifies regularity for `r₂'` with
   regularity for `r₂` at the same parameter. So `S`-regularity of `parameterRestrict e λ` for
   `r₂` gives `S`-regularity of `λ` for `s`, hence `R`-regularity for `r₁` by step 5.

## Relation to the literature

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math.
Soc. 37 (2024), §2.2, p. 191 (registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`), measure the regularity of `λ` by
`⟨Re λ, α^∨⟩ ≫ 0` for the simple roots `α` of `P`. That condition depends only on the parabolic.
The theorem shows that the Library's presentation-dependent regularity predicate
`ParabolicRootPresentation.IsRegularParameter` defines the same notion of "sufficiently
regular", up to a change of threshold. The comparison of thresholds for one parabolic with two
isomorphic tori is `eisensteinRegularityTorusComparison`. It rests on the identity
`B(x, β) = ⟨x, β^∨⟩ · B(β, β) / 2` for Weyl-invariant forms. This module adds the conjugation of
maximal split tori inside the common Levi and the change of the parabolic and split-component
models.
