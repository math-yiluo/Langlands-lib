# Original stalks of equivariant inverse image

Worker 151, Task 5297. Derived construction supporting Renard III.3.2,
printed p.84 / PDF p.90, restriction-functor paragraph and its assertion that
point restriction is the original smooth stabilizer representation. Source:
`renard-2026-representations-groupes-reductifs-padiques`, French edition dated
9 July 2026, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
This unit constructs the comparison between original stalks for the
published action-sheaf inverse image. The comparison is an internal
implementation bridge for the source's restriction, not a separately printed
theorem or a supplied isomorphism assumption.

All names have prefix
`Langlands.Sheaf.Renard.SectionActions.InverseImageStalks`.
The group and both spaces are universe-zero types, and coefficients are
actual complex vector spaces `ModuleCat.{0} ℂ`. The basic comparison assumes
only continuous individual group translations and a continuous equivariant
map f:X→Y. The comparison of the published fixed-stalk actions also assumes
a topology on G and jointly continuous actions, as their existing definitions
do. No local profiniteness, closedness of a subgroup or countability at infinity
is needed for these underlying stalk comparisons. The source's t.d.
continuous-action hypotheses are included; the later homogeneous-space
statements retain their separate hypotheses.

`preimageStalkMap` takes an original transport-presheaf transformation
F→f_*F′ and uses its ordinary stalk map followed by Mathlib's original
`stalkPushforward`. `germ_preimageStalkMap` identifies its value on every
original germ: apply the given section transformation and then take its germ
on the inverse-image open. `preimageStalkMap_transport` proves compatibility
with both original `Godement.stalkPull` maps. Its proof uses the original
labelled inverse-image arrow, the germ formula and the naturality square of
the given transformation. It does not install a transported replacement
action on either stalk.

For the actual transport left Kan extension,
`kanStalkMap_comparison` compares this map, induced by its actual unit, with
Mathlib's ordinary `stalkPullbackHom` after the canonical presheaf comparison
from `InverseImageComparison`. Unit preservation and the two germ formulas
give the equality. The ordinary stalk map is the forward map of Mathlib's
`stalkPullbackIso`; hence `kanStalkMap_isIso` proves invertibility of the
transport map itself.

`sheafifyStalkMap` is the original transport-sheafification unit restricted
to ordinary opens and then evaluated on the original stalk. Restriction
commutes with sheafification by the published continuous/cocontinuous
inclusion comparison. Its compatibility with the actual units expresses this
map as ordinary sheafification's unit followed by an isomorphism. Mathlib's
`stalkFunctor_map_unit_toSheafify_isIso` and this expression establish
`sheafifyStalkMap_isIso`.

`unit` is explicitly the transport Kan-extension unit followed by
precomposition of the transport-sheafification unit. Its target is the literal
published `actionInverseImage`, after the existing transport-sheaf category
equivalence. `stalkMap` is the induced map from the original stalk F_{f(x)}
to the original stalk of that actual inverse-image sheaf at x.
`stalkMap_factor` expresses it as the unsheafified Kan stalk map followed by
the original sheafification stalk map. Thus `stalkMap_isIso` proves it
invertible and `stalkIso` bundles this same map as an isomorphism.
`germ_stalkIso_hom` displays its exact original-section formula.

`unit_naturality` follows from the unit naturality of the composite original
Kan-extension and sheafification adjunctions. The germ formula then gives
`stalkMap_naturality`, on the original induced stalk maps.

For a subgroup Q fixing x, `fixes_image` proves that Q fixes f(x).
`fixedStalkIso` bundles `stalkIso` as an isomorphism of the two existing
`fixedStalkAction` objects. Its commutation law is precisely
`preimageStalkMap_transport` with label q⁻¹, retaining the published convention
that a left stalk action uses the inverse-labelled pullback.
`fixedStalkActionsIso` is this natural isomorphism in the action category;
`fixedStalkFunctorIso` applies the published `Rep.ActionToRep` functor to give
it in the existing representation category. Its source is the original
fixed-stalk functor at f(x) and its target is the actual inverse image followed
by the original fixed-stalk functor at x.

This completes the original-stalk and stabilizer-action comparison for the
actual inverse image. It does not yet construct the equivalence between
sheaves on a singleton and representations, compare singleton global sections
with their stalk, lift this natural isomorphism to the smooth categories, or
construct the induction/coinvariant sheaves or the main III.3 statements.
