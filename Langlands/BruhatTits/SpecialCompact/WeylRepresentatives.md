# Relative Weyl representatives in a special-point parahoric

Author: Worker 102. Extracted by Integrator from the published
`Langlands.BruhatTits.Iwasawa.AvailableProof`; the accepted Cartan proof carried
the same four arguments. Their statements and proofs are preserved, and the
final theorem is shared by both consumers.

`Langlands.BruhatTits.SpecialCompact.WeylRepresentatives.special_parahoric_normalizer_surjective`
states that every relative Weyl group element has a representative in
`N(F) ∩ B.parahoricAt x`. The hypotheses are a nonarchimedean local field,
parahoric building data, the apartment axioms, zero-fixer generators, rank-one
factorization, a generic cocharacter, and specialness of `x`.

## Special-point normalizer representatives

The internal lemma `linear_reflection_eq_of_ker_eq` proves that two coroot
reflections preserving the finite derivative-root set have the same linear
part when their root forms have the same kernel. It first expresses one
form as a real multiple of the other. Mathlib's
`Module.Dual.eq_of_preReflection_mapsTo`, applied to the finite spanning
set of derivative roots, then identifies the appropriately scaled coroots.
This argument includes the rank-zero case.

For an affine root vanishing at `x`, `exists_parahoric_reflection` uses
`reflectionAffineRoots_eq` and the published `rootRankOneFactorization` to
choose an actual opposite pair. The Library results
`isCoroot_reflectionCoroot`, `normalizerAffineEquiv_reflectionElement` and
`reflectionElement_mem_simplyConnectedImage` identify its apartment action
and place it in the simply connected image. It fixes `x`, hence belongs to
the actual singleton zero fixer. The available root-group-action axiom,
through `HasZeroFixerGenerators.zeroFixer_le_parahoric`, places it in
`B.parahoricAt x`. The axiom is applied only to the nonempty bounded
singleton `{x}`.

`special_parahoric_normalizer_surjective` applies specialness to the kernel
of each simple root form. The vanishing-root reflection just constructed
has the same linear part as an actual opposite-pair representative of that
simple root. `translationAction_eq_one_iff_mem_centralizerPoints` shows
that their classes in the actual quotient `N(F)/Z(F)` agree. The published
`relativeRootSystem` gives uniqueness of the relative reflection, and
`relativeTitsSystem` gives generation by the simple reflections. The image
of the parahoric-normalizer intersection is therefore the whole relative
Weyl group. No Weyl-surjectivity premise is added.

## Sources and consumers

This is the special-point argument used in the available
[Iwasawa proof](../Iwasawa/AvailableProof.md) and
[Cartan proof](../Cartan/AvailableCartanProof.md). It combines the published
rank-one and relative Tits-system results with KP Lemma 1.3.42 and the
corrected apartment and root-group-action axioms. It asserts no existence
of available building data or of a special vertex.
