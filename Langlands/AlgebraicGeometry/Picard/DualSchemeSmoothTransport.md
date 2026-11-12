# Actual parameter isomorphisms and smoothness transport for a chosen dual scheme

`Langlands.AbelianScheme.dualSchemeIsoOfUniversal` chooses an actual
isomorphism in `Over S` from the existing chosen dual `dualScheme A hA`
to any supplied parameter `P` carrying an actual universal geometric
Picard-zero family `L`. The construction works over every
`S : Scheme.{u}`, for every universe `u`. Its hypotheses are exactly
`A : AbelianScheme S`, `hA : HasDualScheme A`, the actual family
`L : RigidifiedFamily A P` and `IsUniversalPicardZero A L`.

This is a derived construction from the published theorem
`picardZeroUniversalUniqueness`, applied to `poincareFamily A hA` and
`L`, with the published proof `RigidifiedModule.pullbackCoherence`.
`Classical.choose` selects its parameter isomorphism.
`dualSchemeIsoOfUniversal_family` records the existence of an actual
rigidified isomorphism between the pullback of `L` along its forward map
and `poincareFamily A hA`. It does not assert uniqueness of that bundle
isomorphism.

`smooth_dualScheme_iff_of_universal` proves that the two structural
morphisms are smooth together. Applying the forgetful functor
`Over.forget S` shows that both underlying scheme maps of the chosen
parameter isomorphism are isomorphisms. Its slice equations express each
structural morphism as the other structural morphism preceded by an
isomorphism. Mathlib's smoothness of isomorphisms and stability of
smoothness under composition give the two implications.

`dualSchemeIsoOfOpenLocus` applies this construction to
`restrictedRigidifiedFamily A L U`. Here `L` is a supplied full actual
universal rigidified family and `U` satisfies the existing
`IsPicardZeroOpenLocus A L U`. The published
`restrictedRigidifiedFamily_universal` theorem gives the required
Picard-zero universal property. The resulting isomorphism has target
`openLocusParameter P U`, the actual open subscheme with its restricted
structure sheaf. The lemma
`smooth_dualScheme_iff_of_openLocus` transports smoothness in both
directions, and `smooth_dualScheme_of_smooth_openLocus` specializes the
direction used in the eventual field-dual smoothness proof.

These comparisons retain the existing universal properties on **every**
test scheme, including nonreduced schemes. The scheme isomorphism is
obtained from those properties; it is not inferred from equality of
geometric point sets.

The module also collects two elementary helpers for final assembly.
`geometricPointRanges_determine_set` states that two subsets of a scheme
are equal if they have the same range-containment tests for every
`Spec K` with `K : Type u` algebraically closed. For each point `x`, the
proof takes `K = AlgebraicClosure (X.residueField x)` and composes the
spectrum map of the algebra inclusion with `X.fromSpecResidueField x`.
Mathlib's `fromSpecResidueField_apply` proves that this map is constant
at `x`. Its domain contains `IsLocalRing.closedPoint K`, so its range is
exactly `{x}`. The given equivalence then compares membership of `x` in
the two subsets. The residue field and its algebraic closure are both
in universe `u`; no finite type or perfectness assumption is needed.

`isFullPicardIdentityComponentOpen_of_geometric_comparison` compares a
*supplied* all-test Picard-zero open locus with a *separately supplied*
geometric-family/component comparison. It specializes the open-locus
criterion to `Over.homMk s rfl` and uses the definitionally equal
family and class membership predicates. The preceding set lemma then
identifies the open's carrier with the connected component of
`fullPicardOriginPoint k B L hL`, which is exactly
`IsFullPicardIdentityComponentOpen`. This is a downstream adapter. Its
proof must not be used as evidence for the geometric comparison that
it assumes.

The constructions and lemmas do not establish ambient Picard
representability, existence of a Picard-zero open, the geometric-family
comparison, or smoothness of the identity component. In particular,
they do not prove `FieldDualSchemeSmoothStatement`. That exact theorem
remains the parent task's obligation.

The provenance is internal and derived: the new definitions specialize
published universal-property constructions, and the accompanying lemmas
use those constructions and Mathlib's scheme, residue-field and
smooth-morphism APIs. No original-source mathematical theorem beyond
the imported Library results is claimed here.

The transport proofs and the last two helpers are adapted from the
carried shared draft of Workers 511 and 515 of the previous instance for task
`4ef972f8-8ae6-4f1a-b440-857530de2ca6`, revision 1.
Worker 1383 exposes the actual parameter isomorphisms and their family
compatibility, adds the smoothness equivalence for an open locus, and
prepares this focused module and explanation for review.
