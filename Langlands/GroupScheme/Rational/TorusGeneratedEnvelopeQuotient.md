# Restricting a supplied quotient to the fixed torus envelope

This internal construction works at arbitrary universe `u` over every field.
Let `D : TorusGeneratedEnvelope G` be a supplied representative of the fixed
closed envelope of ground-field tori. Assume that `D.group` is smooth and that
the full subgroup functor `range D.inclusion` is normal on every relative
scheme test.

For a supplied pseudo-parabolic inclusion `i : P ⟶ G` and an exact homogeneous
quotient `q : G.X ⟶ Q`, `D.restrictPseudoQuotient` constructs a homogeneous
quotient of `D.group` by the actual scheme-theoretic intersection of `D.group`
and `P`. Its stabilizer inclusion is
`subgroupIntersectionFst D.inclusion i`. The target is definitionally the
original `Q`, and the projection is definitionally `D.inclusion.hom.hom ≫ q`.
The two named equations `restrictPseudoQuotient_scheme` and
`restrictPseudoQuotient_projection` record these identifications.

The original map must be smooth, surjective and quasi-compact, with exact
right-coset fibers on every `T : Over (Spec k)`. The target structure map must
be separated, locally of finite type and quasi-compact. These are precisely
the geometric fields retained by the constructed homogeneous quotient.
Ambient smoothness, connectedness and affineness follow from the unchanged
`IsPseudoParabolicSubgroup i` predicate; they are not additional arguments
of this specialization.

## Implemented derivation

The existing general lemma `range_subgroupIntersectionFst`, imported from
`Derived.CentralIntersectionPullback`, holds over any base scheme.
The published intersection pullback in relative schemes supplies, for every
test scheme, the equivalence between a point of the first factor whose image
lies in the second subgroup and an actual point of the intersection above it.
Thus the range of the first projection equals the full preimage of the
second subgroup. This equality needs no monomorphism assumption.

`D.product_smooth_surjective` treats any closed stabilizer containing
`Dynamic.parabolic χ` for some cocharacter `χ`. It assumes ambient smoothness,
affineness and connectedness, envelope smoothness and the stated normality,
and an exact smooth supplied quotient. Closedness of the stabilizer gives
its monomorphism and affineness. The published identity-fiber comparison
`HomogeneousQuotient.smooth_subgroup_of_smooth_quotient` gives its smoothness
from the original smooth projection. Affineness of the envelope follows
from its closed inclusion.

The already constructed `D.cocharacterFactor χ` has composite `χ` with the
envelope inclusion. It therefore supplies an actual factor for every
relative-test point in `range χ`. The normal-subgroup multiplication theorem
`Dynamic.normal_subgroup_product_smooth_surjective` now proves that
`D.group × P ⟶ G`, in the order `(d,p) ↦ D.inclusion(d)i(p)`, is smooth and
surjective as a scheme morphism. This conclusion asserts no rational
surjectivity of that multiplication map.

`D.restrictQuotient` combines this multiplication geometry with
`HomogeneousQuotientRestriction.restrict` and the preceding full-preimage
equality. The latter adapter retains the supplied target, descends
smoothness along the first product projection, transfers scheme
surjectivity, and obtains quasi-compactness from the closed inclusion. Its
fiber calculation retains the right-coset condition on every relative
scheme, including nonaffine and nonreduced tests.

For `D.restrictPseudoQuotient`, the unchanged pseudo-parabolic predicate
provides closedness and a cocharacter whose dynamic parabolic is contained
in `range i`. These facts discharge the corresponding arguments of
`restrictQuotient`.

`D.restrictDynamicQuotient` covers the case
`range i = Dynamic.parabolic χ` in a smooth connected affine ambient group.
It accepts any supplied representative `j : K ⟶ D.group` of
`Dynamic.parabolic (D.cocharacterFactor χ)`. The previously proved
`D.parabolic_cocharacterFactor χ` identifies this functor with the full
preimage of the original stabilizer. The same restriction adapter therefore
returns a homogeneous quotient for this `j`, again with the original `Q`
and projection precomposed with the envelope inclusion. It does not require
the original dynamic stabilizer to be pseudo-parabolic.

## Provenance and remaining obligations

All assertions are internal consequences of the existing cocharacter
factorization, actual intersection pullback, normal-subgroup multiplication,
identity-fiber comparison and homogeneous-quotient restriction interfaces.
No additional literature theorem is asserted.

The envelope's normality and smoothness are explicit inputs, not conclusions
of this unit. In particular, it does not prove normality of the fixed
envelope, identify a general pseudo-parabolic intersection as a dynamic
parabolic, produce an identity-coset section, prove density, or establish
rational lifting. Those structural and rational-point obligations remain
for the full all-field theorem.
