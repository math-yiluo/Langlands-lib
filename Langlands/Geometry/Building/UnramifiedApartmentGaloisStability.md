# Galois stability of V 6 apartment classes over the maximal unramified extension

Author: Worker 4356.

Lean module: `Langlands.Geometry.Building.UnramifiedApartmentGaloisStability`.

Let `F` be a nonarchimedean local field and `K = inertiaFixedField F` its maximal
unramified extension inside the separable closure, with the published normalized integer
valuation `MaximalUnramified.valuation F` (module `MaximalUnramifiedValuation`). This
module proves that every equipollence class of valuations of the root datum of `(G_K, T_K)`
that satisfies V 6 for the real order of `K`, with respect to some centralizer datum over
`K`, is stable under every `σ : K ≃ₐ[F] K`. This is the Galois-stability input of
Kaletha–Prasad §9.6 (Construction 9.6.1): KP apply `Γ`-equivariance of the building of
`G_K` to the apartment `A(S)`; the Lean proof reduces it to the published Galois-stability
theorem `IntegerValuation.IsOmegaCompatible.galoisStable` (module
`IntegerOmegaGaloisStability`).

The four order-invariance and centralizer-comparison lemmas below are imported
from `UnramifiedOmegaGaloisStable`; this module reuses their existing declarations.
`IsOmegaCompatible.of_centralizerDatum` takes the valuation as an explicit argument.

## Invariance of the order of `K`

- `MaximalUnramified.valuation_galois`: for `σ : K ≃ₐ[F] K` and `x : K`,
  `valuation F (σ x) = valuation F x`.

  Proof. The published `fixedFieldValuation F` equals the spectral valuation
  (`fixedFieldValuation_eq_spectralValuation`, module `SeparableInertiaDefinitions`), and
  Mathlib's `spectralNorm_eq_of_equiv` says the spectral norm is invariant under
  `F`-algebra automorphisms. The published `valuation_isEquiv F` says the normalized
  valuation is equivalent to `fixedFieldValuation F`, so the two inequalities
  `valuation F (σ x) ≤ valuation F x` and its converse follow.
- `MaximalUnramified.order_galois`: for `σ` and `t : Kˣ`,
  `IntegerValuation.order (valuation F) (σ t) = IntegerValuation.order (valuation F) t`.
  This unfolds `order` to `-log (valuation F t)` (`IntegerValuation.orderUnits_toAdd`)
  and applies `valuation_galois`.

## Independence of the centralizer representative (namespace `IntegerValuation`)

Let `k` be a field, `i : S → G` with `S` commutative, `v` an integer-valued valuation of
`k`, and `C E : CentralizerDatum i` two centralizer data. They represent the same
centralizer functor, so `C.isRepresentedBy.isoOfIsRepresentedBy E.isRepresentedBy` is an
isomorphism `e : C.Z ≅ E.Z` with `e ≫ E.j = C.j`, and `C.s ≫ e = E.s` by `hom_ext`.

- `centralizerTranslation_comparison`: for `z : C.Z(k)`, the published
  `centralizerTranslation v C.s C.bijective z` equals
  `centralizerTranslation v E.s E.bijective (e z)` in `V(S)`.

  Proof. `E.bijective` is injective, so it suffices to compare the evaluations of both
  sides at every character `χ` of `E.Z`, restricted along `E.s`. The restriction of `χ`
  along `E.s` is the restriction of `χ ∘ e` along `C.s`. Both sides then reduce to
  `-v(χ(e z))` (`eval_centralizerTranslation`,
  `rationalCharacterEval_characterRestrict`).
- `IsOmegaCompatible.of_centralizerDatum`: if `G` is affine and `i` is a monomorphism,
  `IsOmegaCompatible v D C` implies `IsOmegaCompatible v D E` for every
  `D : KPApartmentData i (order v)`.

  Proof. The map `e` on `k`-points is surjective (`isoPointsEquiv`). For `z : C.Z(k)`, the
  point `e z` of `E.Z` has the same image in `G(k)` as `z`, and by the comparison it has
  the same translation. So the V 6 condition for `E` at `e z` is the V 6 condition for `C`
  at `z`.

## The unramified statement

`unramifiedGaloisStable_of_isOmegaCompatible`. Hypotheses: `G` a connected reductive
`F`-group (`hG`), affine; `T` a commutative `F`-group with `iT : T → G` such that the base
change `iT_K` is a maximal split torus of `G_K` (`hiT`) and a monomorphism; the opposite
factor pairs of `iT_K` (`hE`); `D : KPApartmentData iT_K (order (valuation F))`; a centralizer
datum `C` of `iT_K`; and `h6 : IsOmegaCompatible (valuation F) D C`. Conclusion:
`KPApartmentData.GaloisStable F K iT D`.

Proof.
1. `T` is affine over `F`. `T_K` is affine because it is a split torus, and affineness
   descends along the fpqc morphism `Spec K → Spec F` (Mathlib's
   `MorphismProperty.of_pullback_snd_of_descendsAlong` with the published instance for
   affine morphisms in `SchemeFlatPropertyDescent` and `fieldExtension_fpqc`).
2. The published `fieldCentralizerRepresentability` gives a closed `F`-subgroup
   `j : Z → G` representing the centralizer of `iT`, and the factor
   `s = torusCentralizerFactor iT` with `s ≫ j = iT`.
3. Base change: `j_K` is a closed subgroup (`IsClosedSubgroup.baseChange`) and represents the
   centralizer of `iT_K` (`torusCentralizer_baseChange`, `IsRepresentedBy.baseChange`), and
   `s_K ≫ j_K = iT_K`. `G_K` is connected reductive by
   `connectedReductiveFieldExtensionStatement`.
4. Restriction followed by real evaluation along `s_K` is bijective. The published
   `IsMaximalSplitTorus.restrictionEvaluation_torusCentralizerFactor_bijective` (with the
   proved structural statements `dynamicCentralizerReductive` and
   `centralSplitTorusCharacter`) gives this for the canonical factor of `iT_K` through
   `j_K`, and that factor equals `s_K` by `hom_ext`.
5. Steps 3–4 form a centralizer datum `C'` of `iT_K` from the base change of `(Z, j, s)`.
   `IsOmegaCompatible.of_centralizerDatum` moves `h6` from `C` to `C'`.
6. `IntegerValuation.IsOmegaCompatible.galoisStable` applies, with the invariance of the
   order from `order_galois`.

## Provenance

The setting is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), §9.6
(Construction 9.6.1, Remark 9.6.2, Lemma 9.6.3, printed pp. 364–366). KP's apartment
`A(S)` in `B(G_K)^Γ` is Galois stable because `Γ` acts on the building of `G_K`
compatibly with the valuation. The Lean statement expresses this for any class satisfying
V 6. The lemmas on the order of `K` and on centralizer representatives are existing
inputs reused by this reduction.
