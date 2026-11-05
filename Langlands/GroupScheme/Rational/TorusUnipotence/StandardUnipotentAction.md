# The torus action on the standard unipotent subgroup

Let `G` be a smooth affine group over a field `k` (`[IsAffineHom G.X.hom]`,
`[Smooth G.X.hom]`), `i : T ⟶ G` a homomorphism from a split torus `T`
(`hT : IsSplitTorus T.toGrp`), and `ν` a cocharacter of `T`. Write
`N = Standard.unipotentScheme i ν ∅` for the closed representative of the standard unipotent
subgroup with the empty set of simple roots, with inclusion `ι = Standard.unipotentHom i ν ∅`.
This module shows that `N` is the dynamic unipotent subgroup `U_G(ν)`, that `N` is smooth and
connected, and that `T` acts on `N` by conjugation. It also shows that the Lie weights of this
action are the positive relative roots, with the same multiplicities as in `Lie(G)`, and that
the weight of every nonzero eigenfunction in the augmentation ideal of the coordinate ring of `N`
pairs positively with `ν`.

This is a step of the proof of the Library proposition
`Langlands.GroupScheme.PositiveTorusTriangularCoordinatesStatement`. It supplies the hypotheses
under which `TorusUnipotence.exists_positiveWeight_coordinates`,
`TorusUnipotence.exists_triangular_mul` and `TorusUnipotence.finrank_actionWeightSpace` apply
to `N`.

Notation: `Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)` is the subgroup functor
`U_G(ν)` of points `g` such that `ν(t) g ν(t)⁻¹ → 1` as `t → 0`.
`positiveRelativeRoots i ν` is the set of relative roots `χ` of `(G, i)` with
`⟨χ, ν⟩ > 0`, and `weightSpace i β` is the `β`-weight space of `T` in the Lie algebra of `G`.
For an action `b`, `RelativeRoot.actionWeightSpace b χ` is the `χ`-weight space on the Lie
algebra. `CoordinateWeights.support b` is the set of characters `χ` for which the augmentation
ideal `m` of the coordinate ring itself contains a nonzero `χ`-eigenfunction, in the all-algebra
sense: `f(s · x) = χ(s) f(x)` for points over every `k`-algebra. This is not the set of weights on
`m / m²`, which the Library records separately as `CoordinateWeights.cotangentSupport b`. For
example, for the upper unipotent subgroup of `GL₂` with coordinate `x` and the diagonal torus
with root `α`, `x²` gives the weight `2α` in `support b`, while `m / m²` has only the weight `α`.

All declarations are in namespace `Langlands.GroupScheme.Standard`. Every declaration after the
two instances assumes `[Smooth G.X.hom]` and `hT`.

## Declarations

- Instances: `IsAffineHom (unipotentScheme i ν J).X.hom` (from the Library fact that `ι` is a
  closed subgroup) and `Mono (unipotentHom i ν J).hom.hom` (from representability).
- `standardUnipotent_empty_eq`: `standardUnipotent i ν ∅ = Dynamic.unipotent (groupHom ν ≫ i)`.
- `isRepresentedBy_unipotentHom_empty`: `ι` represents `U_G(ν)`.
- `smooth_unipotentScheme_empty`: `N` is smooth over `k`. This is a theorem, not an instance.
- `connectedSpace_unipotentScheme_empty`: the underlying space of `N` is connected.
- `unipotentAction i ν hT` (a definition): the action `AutomorphicAction T.toGrp N` obtained by
  restricting the conjugation action of `T` on `G` (`AutomorphicAction.conjugation i`) to `N`.
- `unipotentAction_act_comp`: for points `s` of `T` and `x` of `N` over the same test scheme,
  `ι(s · x) = i(s) ι(x) i(s)⁻¹`.
- `actionWeightSupport_dynamicUnipotent`: the weights of conjugation by `T` on the Lie algebra of
  `U_G(ν)` are exactly `positiveRelativeRoots i ν`.
- `actionWeightSpace_unipotentAction_ne_bot_iff`: for every character `χ`,
  `actionWeightSpace (unipotentAction i ν hT) χ ≠ ⊥ ↔ χ ∈ positiveRelativeRoots i ν`.
- `finrank_actionWeightSpace_unipotentAction`: for `β ∈ positiveRelativeRoots i ν`,
  `finrank k (actionWeightSpace (unipotentAction i ν hT) β) = finrank k (weightSpace i β)`.
- `pairing_pos_of_mem_support`: if `χ ∈ CoordinateWeights.support (unipotentAction i ν hT)`,
  then `0 < latticePairing T χ ν`.

## Proofs

`standardUnipotent_empty_eq`. The inclusion `≤` is the Library lemma
`standardUnipotent_le_dynamicUnipotent`, applied to `ν`, which is a standard cocharacter for the
empty set (`isStandardCocharacter_empty_self`). For `≥`, a point `g` of `U_G(ν)` lies in the
standard unipotent subgroup if it lies in `U_G(ζ)` for every standard cocharacter `ζ` for `∅`.
The Library criterion `rootSignUnipotentInclusions` gives `U_G(ν) ≤ U_G(ζ)` provided every
relative root positive on `ν` is positive on `ζ`. For a standard `ζ`, a relative root `χ` with
`⟨χ, ν⟩ > 0` is positive on `ζ` unless it lies in the additive closure of `∅`
(`IsStandardCocharacter.pairing_pos_iff_not_mem_closure`). That closure is `{0}`, and relative
roots are nonzero.

`isRepresentedBy_unipotentHom_empty`. Rewrite with `standardUnipotent_empty_eq` and use the
Library representability of `standardUnipotent i ν J` by `unipotentHom i ν J`.

`smooth_unipotentScheme_empty` and `connectedSpace_unipotentScheme_empty`. Every representative
of `U_G(ν)` is smooth (Library `dynamicSmooth`) and connected
(`DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent`).

`unipotentAction` and `unipotentAction_act_comp`. `U_G(ν)` is stable under conjugation by `T`
(Library `Dynamic.unipotent_isStable_conjugation`), so conjugation restricts to the represented
subgroup (`AutomorphicAction.onRepresentedSubgroup`). The formula is
`onRepresentedSubgroup_act_comp` combined with `AutomorphicAction.conjugation_act`.

`actionWeightSupport_dynamicUnipotent`. By the Library result `dynamicUnipotent_semigroupData`,
`U_G(ν)` is a smooth connected closed subgroup whose Lie algebra is the span of the
`T`-weight spaces of `Lie(G)` with weights in the positive semigroup `{χ | ⟨χ, ν⟩ > 0}`. By
`actionWeightSupport_subset_of_tangentSubmodule_le`, the support of `U_G(ν)` lies in that
semigroup. `actionWeightSupport_eq_inter_of_hasLieImage` then shows that the support is the
intersection of the support of `G` with the semigroup. That intersection is
`positiveRelativeRoots i ν` (`actionWeightSupport_top_inter_positiveSemigroup`).

`actionWeightSpace_unipotentAction_ne_bot_iff`. The weight spaces of the restricted action on
`Lie(N)` are nonzero exactly for the weights in the support of `U_G(ν)` inside `G`
(`mem_actionWeightSupport_iff_onRepresentedSubgroup`). Then apply the previous theorem.

`finrank_actionWeightSpace_unipotentAction`. The tangent map of `ι` is injective
(`Lie.targetMapLinear_injective`). It maps the `β`-weight space of `Lie(N)` onto the
intersection of the `β`-weight space of `Lie(G)` with the tangent space of `U_G(ν)`
(`map_actionWeightSpace_eq_inf_tangentSubmodule`). For positive `β`, the `β`-weight space of
`Lie(G)` lies in the semigroup weight span. By `dynamicUnipotent_semigroupData` and the
representability of `U_G(ν)` by `ι`, it therefore lies in the tangent space of `U_G(ν)`. So the
intersection is the whole weight space, which is `weightSpace i β`
(`actionWeightSpace_conjugation`). An injective linear map preserves `finrank`.

`pairing_pos_of_mem_support`. `N` is smooth, affine and connected, and `T` is split. The Library
theorem `CoordinateWeights.coordinateSemigroupComparison` (its second component) gives, for
every additive subsemigroup `M` of the character lattice:
`support b ⊆ M ↔ actionWeightSupport b ⊤ ⊆ M`. This compares containment in `M` only; it does
not say that the two sets of weights are equal. Take `M = {χ | ⟨χ, ν⟩ > 0}`, which is closed
under addition. The Lie weights of `N` are positive relative roots by
`actionWeightSpace_unipotentAction_ne_bot_iff`, so they lie in `M`. Hence every weight of a
nonzero augmentation eigenfunction lies in `M`.

## Provenance

This is an internal supporting module for the proof of
`PositiveTorusTriangularCoordinatesStatement` (part of the proof of
`NormOneRationalQuotientFiniteVolumeStatement`, Getz–Hahn 2024 Theorem 2.6.3). It specializes
Library results on dynamic subgroups (Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd ed.,
§2.1, in particular Proposition 2.1.8: `U_G(λ)` is smooth and connected, with Lie algebra the
sum of the positive weight spaces) to the standard unipotent subgroup. The comparison with
standard parabolic data uses the Library's root-sign criterion. No new mathematics is
introduced, and no literature proof is followed step by step.
