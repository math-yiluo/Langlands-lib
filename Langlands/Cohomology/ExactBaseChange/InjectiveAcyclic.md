# Exact base change from acyclicity on injective objects

Author: Worker 284.

This is an internal derived construction for the analytic étale and quasi-étale global
comparison proofs. It specializes the published arbitrary-resolution criterion
`ExactBaseChange.isIso_baseChangeNatTrans_app_of_acyclic`. Its proof follows the
injective-resolution argument already implemented for full twisted sheaves in
`TwistedOver.isIso_restrictionGlobalComparison_app`; here the image of an injective need
only be acyclic, rather than injective. No new assertion from the literature is used.

Let `F₁ : C₁ ⥤ D₁` and `F₂ : C₂ ⥤ D₂` be additive functors preserving finite limits between
abelian categories. The source categories have injective resolutions. Let `α : C₁ ⥤ C₂`
and `β : D₁ ⥤ D₂` be additive functors preserving finite limits and homology, and let
`τ : F₁ ⋙ β ⟶ α ⋙ F₂` be a natural isomorphism. Suppose that for every injective `I` in
`C₁` and every `r : ℕ`, the object `(F₂.rightDerived (r + 1)).obj (α.obj I)` is zero.

The component theorem `isIso_baseChangeNatTrans_app_of_injective_acyclic` proves that the
published comparison `(baseChangeNatTrans τ n).app A` is an isomorphism for every object
`A` and degree `n`. It uses an injective resolution `K` of `A` and its image under `α`.
The image augmentation is a quasi-isomorphism because `α` preserves homology. Every term
of `K` is `F₁`-acyclic by injectivity, and each image term is `F₂`-acyclic by the stated
hypothesis. The map of section complexes induced by `τ` is an isomorphism in every degree,
hence a quasi-isomorphism. The published criterion then applies with identity comparison
on the image resolution.

`isIso_baseChangeNatTrans_of_injective_acyclic` assembles the component results into an
`IsIso` instance for the natural transformation. `baseChangeIsoOfInjectiveAcyclic` packages
it as a natural isomorphism
`F₁.rightDerived n ⋙ β ≅ α ⋙ F₂.rightDerived n`. Its forward map is the already published
`baseChangeNatTrans τ n`, by the definition of `asIso`.

The acyclicity premise and the invertibility of `τ` are retained hypotheses. This module
does not prove them for analytic étale or quasi-étale sheaves, and does not prove either
analytic global comparison statement.
