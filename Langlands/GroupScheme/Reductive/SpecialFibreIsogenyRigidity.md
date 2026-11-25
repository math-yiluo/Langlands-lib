# Rigidity of the specified fibrewise isogeny

`fieldFibreIsoOfSpecialFibreIso` constructs an actual isomorphism on each
algebra-valued field fibre of a specified fibrewise isogeny of reductive
group schemes over a strictly Henselian local ring, provided the specified
special-fibre map is an isomorphism. Its forward map is exactly the actual
base change of the supplied homomorphism `f`, as recorded by the `_hom`
lemma. The field and all rings and schemes lie in one arbitrary universe.
The construction assumes neither that the local ring is a domain nor that
it is a discrete valuation ring, and the field may be any algebra over it.

The module first proves `isIso_fieldFibre_of_specialFibreIso`. It uses the
published local special-fibre predicate for base change along the quotient
homomorphism to the residue field. Fibrewise isogeny means finite, flat and
surjective on every canonical residue-field fibre; the actual field-point
transport theorem transfers this property to the chosen field algebra.

For the specified map, local Nakayama and smooth actual Lie scalar extension
make its differential surjective over every coefficient algebra. Naturality
of the actual scheme-pullback Lie comparison gives surjectivity of the
chosen field-fibre homomorphism's actual differential. The published
square-zero lifting criterion then makes that homomorphism smooth.
Its full scheme-theoretic kernel is central by `SmoothFiniteKernel`.
Thus it is a central isogeny, with local finite presentation supplied by
smoothness.

The common coordinate maximal torus obtained from the specified
special-fibre isomorphism is maximal in the chosen field fibre. Use its
actual pullback as the source torus, and the actual pullback of its composite
with `f` as the target embedding of the same torus. The restriction is the
identity on this torus. A maximal torus in a connected reductive group is
its own all-test centralizer; the published central-isogeny restriction
criterion therefore makes the specified field-fibre map an isomorphism.
The definition packages this map and its inverse as an actual group-scheme
isomorphism.

Finally `strictHenselianDVRIsogenyRigidity` has exactly the
published type `StrictHenselianDVRIsogenyRigidityStatement`. It specializes
the preceding theorem to the fraction-field algebra of a strictly
Henselian discrete valuation ring. The additional DVR and fraction-field
assumptions are unnecessary for the stronger local result but remain
in the published interface.

This construction is an internal composition of the Library's reductive
field-fibre transport, common maximal-torus existence, differential
smoothness and self-centralizing restriction results, together with the
paired smooth finite-kernel centrality proof. The fieldwise-isogeny
transport comes from `Reductive.FibrewiseIsogenyBaseChange`. This module does
not prove the arbitrary-base `ReductiveFibrewiseIsogenyStatement`: removal of
the finite special-fibre kernel and the global finiteness reductions are not
part of it. That statement is proved as `reductiveFibrewiseIsogeny` in
`Reductive.FibrewiseIsogenyProof`.
