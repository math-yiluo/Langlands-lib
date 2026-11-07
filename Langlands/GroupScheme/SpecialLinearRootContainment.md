# Full split special-linear images in subgroups containing ambient roots

This internal comparison works over every field `k : Type u`, in arbitrary
characteristic, with any finite matrix index type `n : Type`. The source is
the actual `SpecialLinear.groupScheme n (CommRingCat.of k)`, or an actual
model `A` with a specified ground-field isomorphism to that group scheme.
Every map to the actual target group scheme `G` is a group-scheme
homomorphism.

For a map `f : SLₙ ⟶ G` and an abstract subgroup `K ≤ G(k)`,
`rationalPoints_range_le_of_coordinate_dynamics` assumes that `K` contains
the rational points of the dynamic unipotent subgroup for every composite
`cocharacter R hrs ≫ f`. Here `hrs` ranges over distinct matrix indices,
and the cocharacters are the actual diagonal constructions in
`SpecialLinearDynamicRoots`. The conclusion is that the entire image of
the actual rational-point map of `f` lies in `K`. This comparison requires
neither normality of `K` nor affineness or reductivity of `G`.

The proof takes the inverse-image subgroup
`K.comap (rationalPoints.map f)`. The explicit all-test contraction puts each
actual coordinate-root image in its source dynamic unipotent subgroup.
The existing `Dynamic.unipotent_le_comap` transports this membership along
`f`. The assumed dynamic containments therefore put all actual coordinate-root
images in the inverse-image subgroup. Ordinary rational root generation from
`SpecialLinearRootGroups` makes that subgroup the whole SLₙ point group.
This argument also covers empty and singleton index types.

The comparison `rationalPoints_range_le_of_iso_coordinate_dynamics`
applies this result to `e.inv ≫ a`, where `e : A ≅ SLₙ` is a supplied
ground-field isomorphism and `a : A ⟶ G` is an actual map. An actual point
of `A` is recovered by applying `e.inv` to its image under `e.hom`, so the
conclusion is the full-image containment for `a` itself.

For the ambient-root specialization, the inputs remain explicit:

- `G` is affine and connected reductive, and `i : S.toGrp ⟶ G` is an actual
  maximal split torus.
- `SmoothMaximalSplitTorusConjugacyStatement.{u}` holds.
- For every cocharacter of `S`, distinct indivisible positive roots have
  disjoint positive integral rays, in the displayed `cyclicTail` sense.
- `K` is normal and contains the rational points of every actual
  relative-root subgroup at `i`.

The existing `dynamicUnipotent_le_normalSubgroup_of_root_groups` supplies
each coordinate dynamic containment with precisely these inputs. The theorem
`rationalPoints_range_le_normalSubgroup_of_root_groups` consequently gives
full-image containment for every actual `SLₙ ⟶ G`. Its `_of_iso` variant
gives the same conclusion for the specified actual split model `A`.

The definition `rationalPointsToNormalSubgroupOfRootGroups` uses the proved
containment to restrict the codomain of the original actual point map to
`K`. Its coercion formula
`rationalPointsToNormalSubgroupOfRootGroups_apply_coe` identifies the
resulting value in `G(k)` with `rationalPoints.map a x`.

The provenance is internal composition of explicit coordinate-root
contractions, actual rational root generation, dynamic functoriality and
the existing ambient dynamic-containment theorem. The ambient structural
inputs and the specified source isomorphism remain premises. This unit
does not require parabolic-dynamic presentation, centralizer reductivity,
source reductivity or containment of all source parabolic-radical images.
It does not construct split models of arbitrary factors, settle nonsplit
rank-one arithmetic, prove the retained ambient structural inputs, or
prove the unrestricted local Kneser–Tits statement.
