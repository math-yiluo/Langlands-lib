# Coherence of degreewise comparison across two exact factorizations

This is an internal construction for abelian categories `A`, `B`, `B'`,
`C` and `E`, with injective resolutions in the first four categories.
Their object and morphism universes are independent.

Let `F₁ : A ⥤ B` and `F₂ : B ⥤ C` be additive functors preserving finite
limits. Let `G : C ⥤ E`, `H : B ⥤ E`, and `K : A ⥤ E` be additive, with
specified natural isomorphisms `e : F₂ ⋙ G ≅ H` and `e₁ : F₁ ⋙ H ≅ K`.
For `N : A`, supply vanishing of the positive derived functors of `F₁` on
`N` and of `F₂` on `F₁ N`.
`twoStepComparison G e e₁ N h₁ h₂ n` is the composite of the existing
canonical `compComparison` maps

`R^n K(N) → R^n H(F₁ N) → R^n G(F₂(F₁ N))`.

This definition requires neither preservation of homology by `F₁` and
`F₂` nor preservation of injectives or finite limits by `G`, `H` or `K`.

For `twoStepComparison_factorization`, supply a second pair
`F₁' : A ⥤ B'`, `F₂' : B' ⥤ C`, its additive functor `H'`, its specified
section isomorphisms `e'` and `e₁'` with the same `G` and `K`, the analogous
two vanishing hypotheses, and a natural isomorphism
`c : F₁ ⋙ F₂ ≅ F₁' ⋙ F₂'`.
All four factor functors must preserve both finite limits and homology.
The compatibility hypothesis states that, for every `Q : A`,

`e₁.inv.app Q ≫ e.inv.app (F₁.obj Q) ≫ G.map (c.hom.app Q)`

`= e₁'.inv.app Q ≫ e'.inv.app (F₁'.obj Q)`.

The theorem proves that the first two-step comparison, followed by
`(G.rightDerived n).map (c.hom.app N)`, equals the second two-step
comparison, in every nonnegative degree. No injective-preservation
hypothesis on the factor functors is used.

The proof chooses one injective resolution `I` of `N`, and maps its
augmentation along each factorization. Preservation of homology makes
all these mapped augmentations right resolutions. The private
`mapResolutionAugmentation_comp` identifies a twice-mapped augmentation
with the mapped augmentation for the composite; the private congruence
lemma supplies compatibility with `c`. The published
`resolutionComparison_naturality` compares the final augmentations.
Termwise section-map compatibility gives an equality of cochain maps,
then an equality on their homology. The comparison from the source
resolution `I` is invertible, since it is the inverse of the canonical
`I.isoRightDerivedObj K n`. Cancel it and apply
`resolutionComparison_compComparison` twice along each route. The homology
identity and naturality finish the proof.

The provenance is internal: this is a degreewise consequence of the
existing actual resolution comparisons. It is related to the more general
`derivedCompComparison_comp_factorization` in `DerivedComparisonComposite`,
which compares actual maps in a derived category under a different set of
acyclicity assumptions. Here preservation of homology by the four factor
functors gives a direct proof with no chosen derived-category instances.
Specialization to scheme-module forgetting and pushforward, comparison
with Ext-defined abelian-sheaf cohomology, actual obstruction naturality,
and the exact field Picard-stack atlas remain further obligations.
