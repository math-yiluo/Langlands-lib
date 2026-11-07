# Full Weil-restricted special-linear images in subgroups containing ambient roots

For a finite field extension `E/F` in arbitrary universe `u` and a finite
index type `n : Type`, this internal unit proves containment of the entire
actual rational-point image of `Res(E/F) SLₙ` in a subgroup of an ambient
group. It combines the proved ordinary generation by actual restricted
coordinate-root images with their explicit all-test contractions.

The theorem `WeilRoot.rationalPoints_range_le_of_coordinate_dynamics`
considers an actual group-scheme homomorphism
`f : WeilRoot.groupScheme F E ⟶ G` and any subgroup
`K ≤ rationalPoints G`. Its premise says that, for every pair of distinct
indices, the rational points of the dynamic unipotent subgroup for the
actual composite `cocharacter F E hij ≫ f` belong to `K`.
Its conclusion is `(rationalPoints.map f).range ≤ K`.
This criterion needs no normality, affineness or reductivity assumption
on the ambient group.

The proof takes the inverse image of `K` under the actual point map.
The theorem `root_range_le_dynamicUnipotent` puts every restricted
coordinate-root point in its explicit source dynamic subgroup.
Functoriality of the actual orbit extension sends it into the composite
ambient dynamic subgroup. The displayed premise therefore places every
restricted root image in the inverse image of `K`.
The proved `eq_top_of_root_images F E` makes this inverse image the full
source point group, giving the desired range containment.

The theorem `rationalPoints_range_le_of_iso_coordinate_dynamics` gives
the same criterion for an actual group scheme `A` with a supplied
group-scheme isomorphism `e : A ≅ Res(E/F) SLₙ`.
It applies the first criterion to `e.inv ≫ a` and transports each actual
point through `e.hom`. The isomorphism is a visible input; the unit does
not construct a model for an arbitrary group.

The ambient-root specialization
`rationalPoints_range_le_normalSubgroup_of_root_groups` assumes an affine
ambient group morphism, connected reductivity of `G`, an actual maximal
split torus `i`, the existing smooth maximal-split-torus conjugacy
statement, and disjointness of the distinct indivisible positive-root
tails for every torus cocharacter. It also assumes that `K` is normal
and contains the rational points of every actual ambient relative-root
subgroup. The existing theorem
`dynamicUnipotent_le_normalSubgroup_of_root_groups` then discharges the
dynamic containment premise for each constructed composite cocharacter.
The result contains the full restricted special-linear source image.
All these ambient structural inputs remain explicit.

The theorem with suffix `_of_iso` gives this specialization for the
supplied actual model `A`. The definition
`rationalPointsToNormalSubgroupOfRootGroups` uses the proved containment
to restrict the codomain of the actual point homomorphism to `K`;
its coercion formula is definitional.

The provenance is internal composition of the actual restricted-root
generation, explicit contraction, dynamic functoriality and existing
ambient-root containment theorem. No parabolic decomposition or source
radical-containment premise is used. The ambient structural inputs,
general factor-model classification, and the unrestricted local
Kneser–Tits theorem are not proved by this unit.
