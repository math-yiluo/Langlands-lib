# Proper finitely presented scheme covers from weak Chow covers

This internal unit derives `ProperSchemeCoverStatement` from the weak Chow
cover interface `ProperSchemeCover.ChowCoverStatement`. It follows the route
described in the task context: first a Noetherian model of the space, then
the cover of that model, then pulling the cover back to the original base.
The cover itself is the hypothesis `h`. The interface is in the spirit of
Stacks Lemma 69.18.1 (Tag 089I); see `ChowCoverStatement.md`.

## Separatedness lemmas

`isSeparated_of_isSeparatedMorphism_structural` says that a space X over S is
separated (`IsSeparated X`, a closed-immersion absolute diagonal) when its
structural morphism is separated in the sense of `IsSeparatedMorphism`. By
`BaseComposition.diag_iff_diagonal_terminal`, the absolute diagonal has the
relative closed-immersion property W exactly when the map to the terminal
presheaf has the W-diagonal property. The structural morphism is that map up
to the isomorphism between the base presheaf and the terminal presheaf
(`basePresheafIsTerminal`).

`isSeparated_hom_of_relative` takes a separated space X over S, a scheme U
over S and a map a : h_U ⟶ X whose base changes to schemes are separated
morphisms of schemes. It concludes that U → S is separated. Again let W be the
relative closed-immersion property of presheaf maps. The proof has three
steps.

1. The relative diagonal of a has W. Let V be the represented pullback of a
   along itself. The diagonal δ : U ⟶ V, with both components the identity,
   is a section of the second projection V → U. That projection is a
   separated scheme morphism by hypothesis, so δ is a closed immersion by
   Mathlib's `IsClosedImmersion.of_comp`. Then `MorphismProperty.relative_map`
   shows that h(δ) has W. Followed by the pullback comparison isomorphism,
   h(δ) is the relative diagonal of a.
2. The map from X to the terminal presheaf has the W-diagonal property, by
   separatedness of X and `diag_iff_diagonal_terminal`.
3. Diagonals of a property stable under base change and composition compose.
   So the composite of a with the map to the terminal presheaf, which is the
   map from h_U to the terminal presheaf, has the W-diagonal property. Hence
   the absolute diagonal of h_U has W. The published
   `isSeparated_of_representableBy`, applied to the tautological
   representation of h_U by U, gives separatedness of U → S.

`relative_comp_iso` says that a relative property of a presheaf map, for a
property of schemes that respects isomorphisms, survives composition with a
presheaf isomorphism.

## The reduction

`properSchemeCover_of_chowCover` proves
`ProperSchemeCover.ChowCoverStatement.{u} → ProperSchemeCoverStatement.{u}`.
Let S be affine and X a space over S. Assume that X has an atlas that is
locally of finite presentation and quasi-compact, and that the structural
morphism of X is proper. The quasi-separatedness hypothesis of the target
statement is not used.

1. The structural morphism is separated, so X is separated.
   `exists_noetherian_model` (`ProperCoverFPApprox`) gives a Noetherian ring
   R, g : S ⟶ Spec R, a separated space X₀ over Spec R with such an atlas,
   and an isomorphism e from `baseChange g X₀` to X.
2. The hypothesis, applied to Spec R and X₀, gives U₀ over Spec R and a
   surjective a₀ : h_{U₀} ⟶ X₀ whose base changes to schemes are proper, with
   U₀ → Spec R locally of finite type. The relative proper property implies
   the relative universally closed and the relative separated properties, by
   `MorphismProperty.relative_monotone`. `isSeparated_hom_of_relative` then
   shows that U₀ → Spec R is separated. Spec R is Noetherian, so U₀ → Spec R
   is locally of finite presentation (Mathlib instance).
3. The cover over S is U = U₀ ×_{Spec R} S (`Over.pullback g`) with
   a = `restrictAtlas g a₀` followed by e. Surjectivity and relative universal
   closedness pass to a by `relative_restrictAtlas` and `relative_comp_iso`.
4. U → S is separated, locally of finite type and locally of finite
   presentation, by base change of the corresponding properties of
   U₀ → Spec R. It is universally closed by
   `universallyClosed_of_relative_of_structural` (`ProperCoverFPComposite`),
   because a is relatively universally closed and the structural morphism of
   X is universally closed. Hence U → S is proper, and a is surjective.

## Provenance

The reduction is internal and follows the route in the task context. It uses
published Library results: model existence along cofiltered limits, base
change of atlases, and `isSeparated_of_representableBy`. It also uses the
units `ProperCoverFPApprox` and `ProperCoverFPComposite`. It does not use
`SpaceLimitPropertyDescentStatement`, and it adds no hypothesis to
`ProperSchemeCoverStatement` beyond the explicit interface `h`.
