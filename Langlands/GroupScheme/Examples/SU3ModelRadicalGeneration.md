# Parabolic radical generation for actual SU3 models

This internal derived unit packages the proved actual SU3 and Weil-restricted
SU3 image theorems for use with actual source models. It imports
`SU3WeilAmbientGeneration`, which also imports `SU3AmbientGeneration`.
Every use of a model supplies an actual ground-field group-scheme isomorphism;
this unit does not construct such an isomorphism by classification.

In `SchemeModel` the assumptions are fields `k` and `L` in any common universe,
with a separable quadratic `k`-algebra extension `L`. In `WeilSchemeModel` there
is also a field `F` and a finite dimensional `F`-algebra extension `k`.
Neither namespace imposes a field-characteristic condition. The restricted
namespace needs no separability hypothesis on `k/F` or `F`-algebra structure on `L`.

In each namespace `rationalPoints_range_le_of_iso_upper_dynamic` takes an actual
isomorphism from a model `A` to the constructed SU3 source and an actual morphism
`a : A ⟶ G`. A normal subgroup of `G`'s rational points containing the dynamic
unipotent subgroup of the original cocharacter composed with `e.inv ≫ a`
contains the whole rational image of `a`. Apply the existing canonical-source
theorem to `e.inv ≫ a` and represent an arbitrary model point by its image under
`e.hom`; the inverse identities cancel the two isomorphism maps.

For a connected reductive target, the existing containment of every dynamic
unipotent subgroup in `parabolicElementarySubgroup` discharges that normal
subgroup premise. The resulting containment uses the original rational-point
map of `a`. `rationalPointsToParabolicElementarySubgroup` restricts its codomain,
and its coercion lemma confirms that the underlying point map is unchanged.
There is no source reductivity requirement for these image theorems.

If the model `A` itself is connected reductive, apply the image theorem to
`a = 𝟙 A`. This proves `parabolicElementarySubgroup A = ⊤`.
Consequently every subgroup `N` containing the rational images of the represented
geometric unipotent radicals of every actual rational parabolic of `A` is the
whole rational group. This last statement uses the existing least-subgroup
characterization of `parabolicElementarySubgroup`. It requires no normality
assumption on `N`, topology, or local-field hypothesis.

All proofs are compositions of previously constructed actual point maps,
inverse isomorphism identities and subgroup inclusions. The explicit model
isomorphism and connected reductivity hypotheses in the last two theorems are
retained. Source reductivity, the classification of general local rank-one
groups into actual sources and the unrestricted local Kneser–Tits theorem
remain separate obligations.
