# Equivariant functoriality of abstract dynamic subgroup functors

This internal helper module compares the actual dynamic functors of two
multiplicative-group actions along an equivariant group-scheme homomorphism.
The base is any scheme B, and all claims are on every scheme over B.

`AutomorphicAction.IsEquivariant a b f` means that f intertwines the actual
point actions of a and b on every test scheme. This predicate is defined for
any common acting group scheme. The remaining declarations specialize the
acting group to the actual multiplicative group.

`IsEquivariant.orbit_comp_hom` identifies the target orbit of the image with
the source orbit followed by f. Composing affine-line extension morphisms
with f preserves orbit extensions and their zero evaluations, which proves
`isOrbitExtension_comp_hom`, `hasLimit_comp_hom`, and the parabolic and
identity-limit inclusions `parabolic_le_comap` and `unipotent_le_comap`.
Constancy of the orbit proves `centralizer_le_comap`; cancellation of a
monomorphism proves `centralizer_eq_comap_of_mono`.

For a closed embedding, `exists_isOrbitExtension_of_isClosedSubgroup` applies
the published `AffineLine.exists_lift_of_unitInclusion` to lift any extension
of an image orbit. Its restriction to the multiplicative group already
factors through f by equivariance. Cancellation of the closed immersion
shows the lift is an extension of the source orbit. Zero evaluation gives
`exists_hasLimit_of_isClosedSubgroup` and `hasLimit_comp_hom_iff`.

These lift and reflection results prove `parabolic_eq_comap_of_isClosedSubgroup`,
`unipotent_eq_comap_of_isClosedSubgroup`, and
`centralizer_eq_comap_of_isClosedSubgroup`. The three `range_inf_` lemmas
restate these preimage equalities as equality of the source image with the
intersection of the target functor and the range of f. No separatedness,
field, smoothness, connectedness, or representability hypothesis is used.

The provenance is internal: these are consequences of the published actual
action and affine-line extension constructions in `Dynamic.Action` and
`Dynamic.ClosedSubgroup`. The proof follows the latter module's closed-subgroup
lifting argument with the orbit identity supplied by equivariance. This unit
supplies a transfer interface for an abstract action embedded into conjugation;
it asserts neither existence of such an embedding nor the cyclic root
comparison or geometric structure of the dynamic functors.
