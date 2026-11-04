# Signed dynamic tangent dimensions under closed inclusions

This internal contribution by Worker 1547 implements a dimension step in the
prescribed-Borel approach proposed by Worker 317. It works with actual Lie
modules, subgroup functors on all scheme tests, and actual homomorphisms between
represented subgroups. All field results hold over any field `k : Type u`, in
every characteristic. The final theorem does not require the ambient groups to
be connected, solvable, or reductive.

## Signed decomposition

For an affine locally finite type group scheme `G` over `k`, a split torus `S`,
an automorphic `S`-action `b` on `G`, and a cocharacter `ν`,
`RelativeRoot.finrank_signed_semigroupWeightSpans` proves

```
finrank (positive weight span for ν)
  + finrank (zero weight span for ν)
  + finrank (positive weight span for -ν) = Lie.dimension G.
```

The weights are the actual characters of `S` in its action on `Lie(G)`, and the
sign is that of the integral character–cocharacter pairing. The private lemma
`finrank_signed_weightSums` partitions an internal direct sum into the positive,
zero, and negative regions. Independence makes the positive and zero spans
disjoint and also makes their sum disjoint from the negative span. Integer
trichotomy makes their sum the whole module. Applying the submodule dimension
formula twice proves the displayed identity. The public weight-span theorem
applies this argument to the published split-torus weight decomposition.

For conjugation through `i : S.toGrp ⟶ G`,
`RelativeRoot.tangentSubmodule_centralizer_eq_semigroupWeightSpan` identifies the
intrinsic tangent submodule of the dynamic centralizer with the zero pairing
span, using the exact dynamic Lie formula. Together with the published signed
unipotent tangent identifications, this gives
`RelativeRoot.finrank_signed_dynamic_tangentSubmodules`: the tangent dimensions
of `U(ν)`, `Z(ν)`, and `U(-ν)` sum to `Lie.dimension G`. Here `U` denotes the
actual dynamic subgroup defined by an identity limit under conjugation, and
`Z` denotes the dynamic centralizer.

## Monotonicity and codimension

For affine groups `H`, `G`, subgroup functors `F`, `F'`, an actual homomorphism
`j : H ⟶ G`, and an all-test inclusion `F ≤ F'.comap j`,
`RelativeRoot.tangentSubmoduleMap` restricts the actual differential of `j` to a
`k`-linear map between their intrinsic tangent submodules. This construction
requires no local finite type hypothesis. If the underlying morphism in the
slice category is monic, `tangentSubmoduleMap_injective` proves injectivity from
the injectivity of the actual differential.
`finrank_tangentSubmodule_le_of_le_comap` then proves tangent-dimension
monotonicity when `G` is locally of finite type, so the target Lie module is
finite dimensional.

For affine locally finite type `H`, `G`, a split torus map `i : S.toGrp ⟶ H`,
and a monic `j : H ⟶ G`,
`RelativeRoot.signed_dynamic_dimensions_of_codimension_le_one` assumes
`Lie.dimension G ≤ Lie.dimension H + 1`. Writing `pH`, `pG` for the positive
dynamic tangent dimensions and `nH`, `nG` for the negative ones, it proves

```
pG ≤ pH + 1 ∧ nG ≤ nH + 1 ∧ (pG = pH ∨ nG = nH).
```

Functoriality gives monotonicity of all three pieces, including the zero
piece. The two signed decomposition identities and the ambient dimension bound
then imply the conclusion by arithmetic. No identification of the two dynamic
centralizers is assumed.

## Actual maps and the equality case

Over any base scheme, `SubgroupFunctor.IsRepresentedBy.mapHom` constructs the
actual map `U ⟶ V` from representatives `i : U ⟶ H`, `j : V ⟶ G`, an ambient
map `b : H ⟶ G`, and `F ≤ F'.comap b`. It uses the represented-subgroup
factorization of `i ≫ b`. `mapHom_comp` proves that the induced map followed by
`j` equals `i ≫ b`. `isClosedSubgroup_mapHom` proves that this map is a closed
subgroup inclusion when `i`, `j`, and `b` are closed subgroup inclusions.

Over a field, `isIso_mapHom_of_finrank_eq` assumes that all four groups are
affine, `U` and `V` are smooth, `V` is connected, and the three supplied
inclusions are closed. Equality of the two intrinsic tangent dimensions implies
that this actual induced map is an isomorphism. The proof identifies each
intrinsic tangent dimension with that of its representing group, then applies
the strict dimension inequality for a proper closed subgroup of a smooth
connected group. An actual closed inclusion is essential to this argument.

## Combined dynamic subgroup theorem

`Dynamic.signed_unipotent_inclusions_of_codimension_le_one` takes a closed
inclusion `b : H ⟶ G` of smooth affine groups over `k`, a split torus map
`i : S.toGrp ⟶ H`, an arbitrary cocharacter `ν`, and
`Lie.dimension G ≤ Lie.dimension H + 1`. It takes four supplied affine closed
representatives: `Upos`, `Uneg` for the two dynamic unipotent subgroups of `H`,
and `Vpos`, `Vneg` for the corresponding subgroups of `G`. It proves

```
Lie.dimension Vpos ≤ Lie.dimension Upos + 1 ∧
Lie.dimension Vneg ≤ Lie.dimension Uneg + 1 ∧
(IsIso (induced positive map) ∨ IsIso (induced negative map)).
```

Smoothness of all four representatives follows from the published dynamic
smoothness theorem; connectedness of the two target representatives follows
from the published dynamic connectedness theorem. Closedness of `b` supplies
monicity. The signed tangent bound gives the two dimension inequalities, and the
equality case gives one isomorphism via the actual induced closed map. The
representatives are supplied rather than chosen or asserted to exist here.

## Provenance and remaining scope

These are internal deductions from the published exact dynamic Lie,
split-torus weight-decomposition, dynamic functoriality, represented-subgroup
factorization, dynamic smoothness and connectedness, and proper closed-subgroup
dimension results. Mathlib supplies independent-sum and finite-dimensional
linear algebra. Worker 317 proposed using signed dynamic inclusions in the
prescribed-Borel route; Worker 1547 supplied the three-part monotonicity
argument, actual maps, proofs, and documentation. No external structural theorem
is asserted by this contribution.

The exact `RankOnePositiveRootUniquenessStatement` remains open. This module
requires the ambient dimension bound as input and does not construct a Borel
quotient, establish its dimension, produce a dominant orbit, or discharge the
remaining normal-solvable-torus and dimension-to-root comparisons. It does not
use the four Borel/dynamic statements excluded by the host task.
