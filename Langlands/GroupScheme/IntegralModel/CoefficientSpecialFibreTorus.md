# Maximal residue tori through coefficient extensions of models

This is an internal derived construction for Task 6009. It combines the
actual coefficient pullback of integral models with the common residue-torus
construction and geometric maximal-torus transport. It does not claim the
prescribed-point building theorem.

Let R and A be local integral domains with a local algebra map R to A, and
let K and L be their fraction fields with compatible scalar towers. The
coefficient extension of a model M is the actual pullback M.baseChange A L.
The residue fields are the actual IsLocalRing.ResidueField types. Their
algebra map is induced by the local coefficient map.

The construction specialFibreCoefficientIso identifies the scalar extension
of M.specialFibre to the residue field of A with the special fibre of
M.baseChange A L. The equality residue_coefficient_square follows from the
composition rule for Spec and the canonical induced residue map. The isomorphism is the comparison of
the two pullback towers in this commuting square. Its naturality theorem
retains the actual model morphism and the actual identity-generic coefficient
extension of that morphism.

Suppose A is a Henselian noetherian valuation domain with algebraically closed
residue field. Let M and N be smooth models of the same K-group, with connected
source special fibre, and let phi be a model morphism inducing the identity
on that K-group. Suppose the L-group is connected reductive. A prescribed
maximal split torus of that L-group is supplied, together with a valuation of
L that is one on A-units and a bound placing its character-valuation kernel
in the integral points of M.baseChange A L.

Then every maximal torus s of M.specialFibre has s followed by
phi.specialFibreMap maximal in N.specialFibre, with the same source torus.
There also exist a maximal torus over the original residue field and its
inclusion s with this property. The closed proposition
`Langlands.GroupScheme.IntegralModel.CoefficientBoundedTorusSpecialFibreStatement.{u}`
records both conclusions with all the hypotheses above. Its proof is
`coefficientBoundedTorusSpecialFibre`.
There is no characteristic restriction, quotient premise, kernel premise,
target connectedness premise or assumed common geometric torus.

The proof first applies the common special-fibre construction to the actual
coefficient-extended model morphism, constructing a common maximal torus over
the residue field of A. The canonical residue comparisons transport that
torus and its composite into the scalar extensions of the original special
fibres. The residue comparison naturality square gives the exact composite
equality. GeometricHomMaximal then applies conjugacy after the algebraically
closed extension and descends maximality of each prescribed original-field
torus. Smoothness and affineness of the residue fibres are obtained by
pullback from the actual models.

For the existential conclusion, the proof uses maximalTorusExistence on the
smooth affine source special fibre over the original residue field. It then
applies the preservation theorem to that torus. It does not descend the
particular torus constructed over the algebraically closed residue extension.

The integral common-torus input is
IntegralModel.Hom.exists_common_maximalTorus_specialFibre_of_bounded from
CommonSpecialFibreTorus. The field-group input is
IsMaximalTorus.comp_of_common_geometric_maximalTorus from GeometricHomMaximal.
The actual identity-generic coefficient extension comes from
UnramifiedComponentModelComparison; the pullback comparison and its
naturality are Descent.squareComparison and
Descent.squareComparison_naturality from SquareSemilinear.
Mathlib's canonical residue-field algebra supplies the induced coefficient
map. These constructions provide the internal provenance of this result.

The retained model, connectedness and boundedness hypotheses must still be
constructed in the building application. This construction neither lifts a
prescribed residue torus to the valuation ring nor supplies the segment or
special-apartment geometry. Task 5514 retains the integral lifting step.
