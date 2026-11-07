# Borel subgroup data inside a dynamic parabolic

Author: Worker 1270.

This internal construction supplies an actual Borel subgroup inside a dynamic
parabolic of a connected reductive group over an algebraically closed field.
The accompanying recognition theorem proves the dynamic-to-geometric direction
of the parabolic classification over every field. All subgroup inclusions and
equalities are inclusions and equalities of the published subgroup functors on
every test scheme.

The selected definition is `dynamicParabolicBorelData`. Its output has type
`DynamicParabolicBorelData χ`, whose data fields are a group scheme `group` and
an actual homomorphism `inclusion : group ⟶ G`. Its certificate fields are
`isBorel : IsBorelSubgroup inclusion` and
`range_le : SubgroupFunctor.range inclusion ≤ Dynamic.parabolic χ`.
The structure is defined for an arbitrary group scheme over a field; the
constructor assumes `IsAlgClosed k` and `hG : IsConnectedReductive G`.
The field, group schemes and test schemes have the arbitrary universe `u` used
throughout the module. No restriction on characteristic is imposed.

## Root support and dynamic containment

`nonnegativeWeightSpan_le_of_root_nonneg` works over any field with any
commutative group scheme `T`, any affine group scheme `G`, any homomorphism
`j : T.toGrp ⟶ G`, and two actual cocharacters `ν, ν'` of `T`.
If every actual root of `j` nonnegative on `ν` is nonnegative on `ν'`, then
`nonnegativeWeightSpan j ν ≤ nonnegativeWeightSpan j ν'`.
The proof handles each character in the defining supremum. The trivial
character has pairing zero with both cocharacters. A character whose weight
space is zero contributes nothing. Every remaining character is an actual
root, so the supplied implication applies. Neither regularity nor splitness
is needed for this linear-algebra lemma.

`parabolic_comp_le_of_root_nonneg` additionally assumes that `T` is split and
`G` is smooth and connected. It proves
`Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j) ≤
Dynamic.parabolic (CommGroupScheme.groupHom ν' ≫ j)` from the same root
inequality. Smoothness provides local finite type. The published
`dynamicLie` and
`iSup_nat_weightSpace_cocharacter_eq_nonnegativeWeightSpan` translate the
linear-algebra inclusion into inclusion of the identity dual-number kernels.
The target cocharacter lies in the source dynamic parabolic because it
factors through the same commutative group, whose points centralize the
source cocharacter. The published
`parabolic_le_parabolic_of_lieKernel` then gives the all-test inclusion.
Its structural arguments are discharged by the actual published proofs
`dynamicSmooth`, `dynamicConnected` and `lieSubgroupEquality`.

`parabolic_regularRefinement_le` applies this criterion to
`regularRefinement hT j ν` and `ν`. The published
`regularRefinement_nonneg` supplies the required direction of root support
inclusion. Thus the dynamic parabolic of the regular refinement is contained
in the original dynamic parabolic.

## Construction of the Borel subgroup

For `dynamicParabolicBorelData hG χ`, the proof first constructs a nonempty
type of witness data and uses classical choice to return actual data.
The published `cocharacterMaximalSplitTorus` factors `χ` through a maximal
split torus `j : T.toGrp ⟶ G`, with cocharacter `ν` and equation
`CommGroupScheme.groupHom ν ≫ j = χ`.
Over the algebraically closed field, the actual proof
`torusFiniteGaloisSplitting` and
`IsTorus.isSplitTorus_of_finiteGaloisSplitting` make every torus split.
Consequently `IsMaximalSplitTorus.isMaximalTorus` proves that this same `j`
is a maximal torus.

Set `refinedCochar := regularRefinement hT j ν` and
`ψ := CommGroupScheme.groupHom refinedCochar ≫ j`.
The nonemptiness proof exhibits a witness whose group and inclusion are
`Dynamic.Affine.parabolicScheme ψ` and
`Dynamic.Affine.parabolicHom ψ`. The regularity certificate
`regularRefinement_isRegular`, the closedness and representability of this
affine representative, and clause 1 of the proved
`regularCocharacterBorel` give its `IsBorelSubgroup` certificate.
The representative's range equality, `parabolic_regularRefinement_le`, and
the factorization equation for `χ` give its `range_le` certificate.
The definition then uses classical choice to select a certified element of
`DynamicParabolicBorelData χ`. Its output has the stated Borel and range
certificates; no identification of its data fields with the exhibited
nonemptiness witness is asserted.

## Recognition over an arbitrary field

`isParabolicSubgroup_of_range_eq_dynamicParabolic` assumes a field `k`, a
connected reductive group `G`, a closed subgroup `i : P ⟶ G`, an actual
cocharacter `χ` over `k`, and
`SubgroupFunctor.range i = Dynamic.parabolic χ`. It proves exactly
`IsParabolicSubgroup i` with the published definition.

The closed immersion is monic, so the range equality makes `i` a representative
of the dynamic subgroup. The published `dynamicSmooth` proves that `P` is
smooth. Base change to `AlgebraicClosure k` preserves connected reductivity by
`IsConnectedReductive.baseChange_of_algebraicExtension`.
`Dynamic.parabolic_baseChange` and `SubgroupFunctor.range_baseChange` transfer
the supplied range equality to that field. Apply the preceding Borel data
constructor there. Its range inclusion becomes inclusion in the range of the
base-changed `i`. The published `SubgroupFunctor.factorOfRangeLE` returns the
actual homomorphism from the constructed Borel group to `P` after base change;
`factorOfRangeLE_comp` gives its required composite equation. These are the
three fields of `IsParabolicSubgroup`: closedness, smoothness, and a geometric
Borel factorization. The proof permits imperfect fields and nonsplit groups.

## Provenance and retained obligation

This is internal derived content from the imported Library modules, with no
additional external source assertion. It combines the published regular
refinement, actual Lie weight sums, dynamic subgroup structure proofs,
cocharacter factorization through maximal split tori, finite Galois splitting
of tori, regular-cocharacter Borel theorem, and range factorization.
It assumes no parabolic classification statement. This contribution supplies
a Borel construction and its certificates, including the reverse implication
of the host equivalence. Constructing a rational cocharacter for an arbitrary
geometrically parabolic subgroup remains the forward obligation of
`ParabolicDynamicStatement`; this module does not assert that full statement.
