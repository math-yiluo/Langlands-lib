# Field parabolic containment with a specified common maximal torus

This is an internal derived ingredient for the arbitrary-base parabolic Lie
containment theorem. It combines the published fixed-torus field classification,
finite Galois descent and dynamic Lie containment criterion. It asserts no new
translation of a numbered source result.

`RelativeLevi.fixedTorusDynamicPresentationOfParabolic` constructs an actual
integral cocharacter of a specified maximal torus contained in a parabolic of a
connected reductive field group. Its subtype property asserts equality of the
parabolic range with the dynamic parabolic of that cocharacter. The torus need
not be split over the original field. The preceding existence theorem proves
this by splitting that very torus over a finite Galois extension, applying the
published fixed-torus split classification and descending its integral orbit
sum. Containment in the parabolic provides the torus factorization by
`IsRepresentedBy.liftOfLE`.

`RelativeLevi.parabolic_range_le_of_lie_le` takes two parabolics in a connected
reductive group over an arbitrary field, together with one specified maximal
torus whose functorial range is contained in both. Inclusion of their actual
`SubgroupFunctor.lie` submodules over that field implies inclusion of the ranges
on all test schemes. It chooses the two fixed-torus presentations just
constructed. The defining cocharacter of the larger parabolic has its range in
the smaller one because both contain the torus. The published theorem
`parabolic_le_parabolic_of_lieKernel`, supplied with `dynamicSmooth`,
`dynamicConnected` and `lieSubgroupEquality`, proves the required containment.
The definition of `SubgroupFunctor.lie` is exactly the membership condition on
actual dual-number identity points needed by that theorem.

`RelativeLevi.parabolicContainmentHomOfLieLE` constructs the resulting group
homomorphism from the smaller parabolic to the larger one by lifting its
inclusion through the represented range. Its companion `_comp` theorem proves
that its composite with the larger inclusion is the smaller inclusion.

The explicit affine typeclass in the tangent-submodule declarations is supplied
by the connected-reductive hypothesis; it expresses no extra geometric
restriction. The construction and theorems apply in every universe `u`, without
splitness, perfectness or characteristic restrictions on the field.
