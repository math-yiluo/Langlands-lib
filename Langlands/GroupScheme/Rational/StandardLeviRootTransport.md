# Root-subset and cocharacter-annihilator transport

This internal construction isolates elementary transport from the structural
standard-Levi comparison. It does not prove `StandardLeviConjugationStatement`.

`cocharacterAut σ` aliases the existing postcomposition action from
[CocharacterAction](../Torus/CocharacterAction.md), sending a cocharacter to
its composite with `σ.hom`. The character action
`characterAut σ` precomposes with `σ.inv`, so cancellation proves
`latticePairing_characterAut_cocharacterAut`, which reuses the shared
`RealTorusSpace.latticePairing_aut`. The image criterion
`annihilates_image_iff` follows from that identity.

`weylAction_image_eq_of_relativeWeylAction_image_eq` recovers equality of actual
character subsets from equality of the exact encoded subsets in the public
target's rational root span. Both subsets must consist of relative roots and the
torus must be split. The proof uses the published
`IsSplitTorus.character_toRat_injective` and the definitional compatibility of
`relativeWeylAction` with `ratAut (weylAction i n)`. It never replaces the encoded
root sets by their linear spans.

`groupHom_cocharacterAut_comp` uses the defining equation for the actual
`normalizingAut i n` to identify postcomposition on torus cocharacters with inner
conjugation after inclusion in the group. This is equality of group-scheme
homomorphisms and applies on every test scheme.

All assertions are internal consequences of the cited published definitions and
elementary category and linear algebra. Finiteness, standard-cocharacter
existence and comparison with a standard Levi require separate proofs; no such
assertion is assumed here. In particular, the root-subset lemma uses only the
injectivity theorem from `RootFiniteness`, whose proof follows from splitting;
it does not use that module's conditional general root-finiteness results.
