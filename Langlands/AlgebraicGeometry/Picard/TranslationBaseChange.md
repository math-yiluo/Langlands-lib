# Translations and base change

Authors: Worker 270 wrote the Lean and initial explanation; Worker 417
checked the interfaces and refined the explanation for submission.

Module `Langlands.AlgebraicGeometry.Picard.TranslationBaseChange` is a helper
module for the proof of
`Langlands.AbelianScheme.FieldDualSchemeMapAdditivityStatement`. It relates
translation by a section of a group scheme `G/S` to translation on a base
change `G_{S'}` along `b : S' ⟶ S`, and deduces two facts about the
Library's geometric-fibre condition `IsGeometricallyPicardZero`.

Here `S` and `S'` are arbitrary schemes in universe `u`; `b` has no
flatness, finiteness or reducedness hypothesis. Line bundles and their
isomorphisms are the existing ordinary, unrigidified `LineBundle` objects.

## Group schemes (`Langlands.GroupScheme`)

* `baseChangePointsEquiv_translation b G σ` computes the translation of
  `G_{S'}` by any section `σ` over `S'`, under the Library group
  isomorphism `baseChangePointsEquiv`. Write `E_T` for that equivalence
  on an `S'`-scheme `T`, and `q : G_{S'} ⟶ Over.mk (𝟙 S')` for the
  structure morphism in the slice. The equation is
  `E_{G_{S'}}(translation G_{S'} σ) =
    ((Over.map b).map q ≫ E_{Over.mk (𝟙 S')}(σ)) *
      E_{G_{S'}}(𝟙 G_{S'})`.
  Its second factor is the point represented by the projection
  `G_{S'} ⟶ G`, obtained from the identity morphism of `G_{S'}`.
  The proof applies `points_translation` to that identity morphism,
  removes identity composition, and uses `map_mul` and naturality of
  `baseChangePointsEquiv`.
* `baseChangeSection b G σ` is the section of `G_{S'}` induced by a section
  `σ : Over.mk (𝟙 S) ⟶ G.X`. It is the inverse image under
  `baseChangePointsEquiv b G (Over.mk (𝟙 S'))` of
  `Over.mkIdTerminal.from _ ≫ σ`.
* `translation_baseChangeSection b G σ`: translation by `baseChangeSection b G σ`
  on `G_{S'}`, followed by the projection `G_{S'} ⟶ G`, equals the projection
  followed by translation by `σ` on `G`. The proof specializes the previous
  equation, cancels the point equivalence with its inverse, identifies
  the maps to the terminal object, and uses `points_translation` for `G`.
* `fibreTranslationIso b G σ F`: for a line bundle `F` on `G`, the
  restriction to `G_{S'}` of the translate `τ_σ^* F` is isomorphic to the
  translate, by the restricted section, of the restriction of `F`. It is
  an actual line-bundle isomorphism
  `p^*(τ_σ^* F) ≅ τ_{σ'}^*(p^* F)`, where
  `p = pullback.fst G.X.hom b` and `σ' = baseChangeSection b G σ`.
  Two applications of `LineBundle.pullbackCompEqIso` implement the
  comparison.

## Abelian schemes (`Langlands.AbelianScheme`)

* `isGeometricallyPicardZero_pullback_translation hF σ`: if `F` is
  Picard-zero on geometric fibres, so is its translate `τ_σ^* F` by any
  section `σ`. On a geometric fibre the translate is isomorphic, by
  `fibreTranslationIso`, to the translate of the fibre of `F`, and the fibre
  of `F` is translation invariant by hypothesis. More precisely, `hF`
  supplies `e : τ_{σ'}^* F_s ≅ F_s`; the composite of `e.symm` with
  `fibreTranslationIso.symm` identifies `F_s` with the restriction of
  `τ_σ^* F`. The Library lemma `isTranslationInvariant_of_iso`
  transports invariance along this composite.
* `isTranslationInvariant_of_isGeometricallyPicardZero K A hF`: over an
  algebraically closed field `K`, an abelian scheme over `Spec K` and a line
  bundle `F` on it that is Picard-zero on geometric fibres, `F` itself is
  translation invariant (`GroupScheme.IsTranslationInvariant`). The proof
  takes the geometric fibre along `𝟙 (Spec K)`, whose total space is the
  pullback along an isomorphism, and uses `LineBundle.isoOfPullbackIso`.
  For each section, `fibreTranslationIso` followed by the isomorphism from
  `hF` gives an isomorphism after this pullback; `isoOfPullbackIso`
  reflects it back to `A`. The algebraic closedness hypothesis is used
  to apply the geometric-fibre condition with the field `K` itself.

## Provenance

These are internal constructions and compatibility proofs derived from the
published `Langlands.AbelianScheme.KernelBaseChange`,
`Langlands.AlgebraicGeometry.Picard.LineBundleIsoLemmas` and
`GeometricPicardZero` modules. The point equivalence is the pullback
adjunction equipped with its existing multiplicative structure;
translation is the existing left translation on group-scheme points.
The line-bundle arguments use functorial pullback and invariance under
isomorphism. No separate literature result or additional geometric
assumption is introduced. This module supplies compatibility for the
separate additivity proof and does not prove its final statement.
