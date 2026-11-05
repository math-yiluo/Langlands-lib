# Closed generation by a split torus and its actual roots

Worker 1437.

This internal construction works over any field `k : Type u`, in every
characteristic. Let `G` be a smooth connected affine group scheme and let
`i : T.toGrp ⟶ G` be a homomorphism from a split torus. Assume explicitly that
the zero adjoint weight space lies in
`RelativeRoot.tangentSubmodule (SubgroupFunctor.range i)`. If a closed subgroup
`d : D ⟶ G` contains the full torus range and every intrinsic relative-root
functor `RelativeRoot.subgroup i α`, then its full range is top.
Neither smoothness nor connectedness of `D` is required. No maximality or
closedness of `i`, algebraic closure of the field, or reductivity of `G`
is an extra hypothesis.

`rootTorusGenerationIso` constructs an actual group-scheme isomorphism
`D ≅ G` under those hypotheses. Its companion
`rootTorusGenerationIso_hom` identifies the forward map with the original `d`.
`range_eq_top_of_torus_and_rootSubgroups` is the all-test fullness result.

The implemented proof uses the following published constructions.

1. For each actual root, the nonzero-character theorem
   `RelativeRoot.subgroup_isSmoothConnectedClosed_of_ne_zero` supplies a
   smooth connected closed representative of its intrinsic root functor.
   Affineness follows from closedness in affine `G`.
2. Index a family by `Option (relativeRoots i)`, using `T` at `none` and
   these representatives at `some α`. The published
   `FiniteGeneration.exists_smooth_generated_family` supplies a smooth
   connected affine closed subgroup `e : H ⟶ G` containing this family,
   minimal among all closed competitors on every test scheme.
3. The split-torus action weight spaces span the actual Lie module.
   The explicit zero-weight hypothesis puts the zero weight in the tangent
   image of `H`. A nonzero character either has zero weight space or is
   an actual root. In the latter case,
   `RelativeRoot.weightSpace_le_tangentSubmodule_subgroup` puts its weight
   space in its root functor's tangent submodule and hence in that of `H`.
   Thus `H` has the full actual Lie image.
4. Since `H` is smooth, the published
   `Lie.isIso_of_surjective_targetMapLinear` makes `e` an isomorphism.
   Every family map also factors through `d`. Minimality of `H` then puts
   its full range in that of `d`, so the latter is top.
5. Uniqueness of representatives of the top subgroup functor gives the
   actual isomorphism `D ≅ G` and the identification of its forward map.

The smooth generated subgroup is used in the Lie-equality step; the proof
does not apply Lie equality directly to the arbitrary closed competitor.
All containment and fullness conclusions concern every test scheme.
The root functors retain all positive integral multiples in the existing
Library convention; no reduced-root restriction is introduced.

The separate lemma
`RelativeRoot.weightSpace_zero_le_tangentSubmodule_range_of_selfCentralizing`
derives the zero-weight inclusion from the supplied all-test equality
`torusCentralizer i = SubgroupFunctor.range i`. This lemma requires only
affineness of `T` and `G` and uses
`Lie.mem_torusCentralizer_of_mem_weightSpace_zero`.
Consequently,
`range_eq_top_of_selfCentralizing_torus_and_rootSubgroups` gives fullness
under that self-centralization equality and the same split-torus and
containment hypotheses.

The provenance is internal composition of the published root-functor,
split-torus weight decomposition, generated-family, actual tangent-image,
Lie subgroup equality, and represented-subgroup interfaces. The
family-generation route also appears in `Cartan.LieGeneration`; its
Cartan-specific hypotheses and conclusions are not used here. No new
literature assertion is made. Neither zero-weight containment nor torus
self-centralization is proved unconditionally in this file. These
conditional constructions do not prove semisimple root generation or
the host task's almost-simple generation statement.
