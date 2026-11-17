# Full star naturality for based root-datum morphisms

This derived internal comparison applies to actual split pinnings and their
full integral root data. `SplitPinning.BasedRootHom p q` retains a root-datum
morphism and the exact correspondence between the two simple supports. Its
lattice maps need not be surjective, so it applies to the root morphisms
associated with central isogenies.

A root-datum morphism intertwines corresponding reflections. Induction on a
Weyl word therefore lifts every target Weyl element to a source Weyl element
intertwining the weight map. Given intertwining automorphisms on the two root
data, lift the target's Weyl correction and compose it with the source's
original automorphism. The resulting source automorphism preserves its base:
its index action is transported to the target's based representative. The
published uniqueness of a based representative in a Weyl coset identifies it
with the source's own correction. This proves `basedProjection_weight` and
`basedProjection_index`.

For actual Galois pinning data, `starAction_weight_of_basedHom` and
`starAction_index_of_basedHom` apply this comparison to the ordinary Galois
actions on the torus characters. They retain every root index and every
chosen Galois element; the same comparison holds simultaneously on all roots.
They allow different ground and splitting fields, provided that the supplied
character-action intertwining holds. No isogeny of group schemes or
character-action compatibility is asserted without its required data.
