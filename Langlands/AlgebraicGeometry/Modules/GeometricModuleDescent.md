# Split effectivity and uniqueness for geometric module descent

This module concerns ordinary module sheaves on arbitrary schemes in one
universe. It uses the existing `Datum`, `Str`, and `Str.Hom` from
`LineBundleFlatDescentStr`. These definitions impose no rank condition:
`Datum p F` supplies natural isomorphisms between the pullbacks of `F` along
every pair of maps with equal composite through `p`, together with their
cocycle law. For `t : T ⟶ Y` and `N : T.Modules`, `Str D t N` supplies
isomorphisms `h* N ≅ g* F` for all scheme tests satisfying `h ≫ t = g ≫ p`,
natural under precomposition and compatible with `D`. `Str.Hom` is the
compatibility condition for actual module morphisms.

`strOfLift D t l hl` constructs a structure on `l* F` whenever
`l : T ⟶ X` satisfies `l ≫ p = t`. On a test `(g,h)` its comparison is the
ordinary pullback composition isomorphism `h* l* F ≅ (h ≫ l)* F`, followed
by `D.θ` from `h ≫ l` to `g`. Naturality follows by transport of composition
isomorphisms and the naturality of `D.θ`; compatibility follows from the
cocycle law of `D`. This construction has no affineness, flatness,
surjectivity, or quasi-coherence hypotheses. `exists_str_of_section`
specializes it to `t = 𝟙 Y`, giving effectivity on the base when a section
`s : Y ⟶ X` of `p` is supplied.

`hom_ext` states that two morphisms between fixed effective structures over
the same `t` coincide if both are compatible. It assumes only that `p` is
flat and surjective; neither module needs to be quasi-coherent. The proof
evaluates both compatibility equations on the actual fibre product
`X ×_Y T`, cancels the target structure isomorphism, and applies faithfulness
of ordinary pullback along its projection to `T`.

`existsUnique_iso` assumes that `p` is affine, flat, and surjective and that
the target module `N'` is quasi-coherent. For two structures on `N` and `N'`
over the same `t`, it gives a unique actual isomorphism `N ≅ N'` whose
forward map satisfies `Str.Hom`. There is no quasi-coherence assumption on
`N` and no rank or finiteness hypothesis. The proof forms the comparison
`γ ≪≫ γ'.symm` on `X ×_Y T`. Naturality and the two cocycle equations show
that its transports agree on every pair of maps with equal projection to
`T`. The canonical equal-composite comparison therefore satisfies
`PullbackHomCompatible`. Affineness of the projection follows by base
change, so `FaithfullyFlatHomDescent.existsUnique_iso` descends this
comparison. `Str.hom_of_universal` promotes the resulting universal
compatibility equation to all scheme tests, and `hom_ext` proves uniqueness.

These are internal derived constructions. Their provenance is the published
transport calculus and structure bookkeeping in `LineBundleFlatDescentStr`,
the ordinary pullback faithfulness theorem in
`FaithfullyFlatPullbackDescent`, and geometric morphism and isomorphism
descent in `FaithfullyFlatHomDescent`. The compatibility calculation for
uniqueness follows the existing rank-one structure calculation; the new
module descent and faithfulness results remove the rank-one assumptions
under the stated hypotheses.

The only object effectivity result here requires a supplied lift or section.
Effectivity for a general geometric cocycle, descent of coherent-family
conditions, and the scheme atlas required by `FieldCoherentStackAtlasStatement`
remain separate obligations.
