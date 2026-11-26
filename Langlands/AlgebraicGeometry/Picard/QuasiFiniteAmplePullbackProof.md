# Proof: ample pullback along quasi-finite separated morphisms

The module `Langlands.AlgebraicGeometry.Picard.QuasiFiniteAmplePullbackProof` proves
`QuasiFiniteAmplePullbackStatement` as the theorem
`Langlands.AlgebraicGeometry.Picard.quasiFiniteAmplePullback`.

## Helper: quasi-compact open immersions

`LineBundle.IsAmple.pullback_of_isOpenImmersion` says the following. Let
`f : Y ⟶ X` be an open immersion that is quasi-compact, and let `L` be ample on
`X`. Then the pullback of `L` along `f` is ample.

- `Y` is quasi-compact, because `X` is quasi-compact and `f` is quasi-compact
  (`QuasiCompact.compactSpace_of_compactSpace`).
- Fix `y ∈ Y`. Ampleness gives a section `t` of a positive power of `L` such that
  `X_t` is affine and contains `f y`.
- The open `f(Y) ∩ X_t` contains `f y`. The Library's section-open basis theorem
  `ampleSectionOpenBasis` gives a section `s` of a positive power with
  `f y ∈ X_s ⊆ f(Y) ∩ X_t`.
- `X_s` is affine. By the Library's `affineGenerationLocusIntersection`, the open
  `X_t ∩ X_s` is affine, and it equals `X_s`.
- The pulled-back section `f^*s` (`LineBundle.pullbackPowSection`) has locus
  `f⁻¹(X_s)` (`LineBundle.sectionOpen_pullbackPowSection`). This locus contains
  `y`. Its image under the open immersion is `f(Y) ∩ X_s = X_s`, which is
  affine. So `f⁻¹(X_s)` is affine (`Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion`).

## Main theorem

Let `f : X ⟶ Y` be locally of finite type, locally quasi-finite, quasi-compact
and separated, and let `M` be ample on `Y`. Mathlib's normalization factors
`f = f.toNormalization ≫ f.fromNormalization`
(`Scheme.Hom.toNormalization_fromNormalization`).

1. `f.fromNormalization` is integral, hence affine. So the pullback of `M` to
   the normalization is ample, by the Library's
   `LineBundle.IsAmple.pullback_of_isAffineHom`.
2. Mathlib's form of Zariski's Main Theorem (`Mathlib.AlgebraicGeometry.ZariskisMainTheorem`)
   gives an instance: `f.toNormalization` is an open immersion. Mathlib also
   gives that it is quasi-compact. So the helper makes the further pullback ample.
3. The Library's `LineBundle.pullbackComp` identifies the iterated pullback with
   the pullback along the composite, which is `f`. Ampleness moves along this
   isomorphism by `LineBundle.IsAmple.of_iso`.

This is the route of Stacks Lemma 37.43.2 together with Lemma 29.38.7. The
quasi-affine case of Lemma 29.38.7 is split into the affine and the quasi-compact
open-immersion cases.
