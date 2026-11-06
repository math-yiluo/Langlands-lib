# Canonical parabolic radical images in dynamic coordinates

This internal construction connects the actual all-test radical used by the
automorphic constant-term family to the existing dynamic identity-limit
subgroup. The field is arbitrary. The ambient group scheme is connected
reductive in the Library's geometric sense. `ParabolicDynamicStatement` remains
an explicit premise; this module does not prove it.

`dynamicParabolicFunctor hPD hG χ` is the actual orbit-extension subgroup
`Dynamic.parabolic χ`, equipped with the geometric parabolicity proved from
`hPD`. `isRationalParabolicRadical_dynamic` proves that the actual
`Dynamic.unipotent χ` is an ambient radical image of this parabolic. Both
subgroups are functors evaluated on every test scheme, rather than only on
rational points.

The implemented proof takes the published affine representatives of both
dynamic subgroups. The all-test inclusion of the identity-limit subgroup into
the orbit-extension subgroup lifts, by the represented-points construction, to
a homomorphism between those representatives. The lift's composite with the
parabolic inclusion is exactly the original unipotent inclusion. The published
unconditional dynamic-centralizer reductivity theorem, composed with
`dynamicGeometricUnipotentRadical_of_centralizer`, proves that this compatible
inclusion is a geometric unipotent radical. The published preservation of
unipotence under field extension and the geometric-to-ground comparison then
prove greatestness over the ground field. No radical or centralizer conclusion
is added as a premise.

`rationalParabolicRadical_dynamic` identifies the canonical chosen radical
image with this identity-limit subgroup by the published uniqueness theorem.
`rationalParabolicRadical_eq_dynamic` gives the same equality for any rational
parabolic whose all-test functor equals the dynamic parabolic. These are
equalities of subgroup functors; they do not choose additional point or measure
comparisons.

The provenance is internal: this unit composes the existing affine dynamic
representability, represented-subgroup lift, centralizer reductivity, geometric
radical reduction, field-extension theorem and canonical radical uniqueness. It
introduces no external theorem. It supplies a structural bridge for the actual
parabolic constant-term family. It contains no properness, finite-volume,
reduction, measure-identification or cuspidal equivalence theorem.
