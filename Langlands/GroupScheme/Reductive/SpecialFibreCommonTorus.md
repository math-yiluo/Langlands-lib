# A common maximal torus from an isomorphic special fibre

Author: Worker 717.

`Langlands.GroupScheme.HasCommonCoordinateMaximalTorus f` records a coordinate
split torus `i : 𝔾_m^I → G` such that both `i` and `i ≫ f` are closed subgroup
embeddings and maximal on every actual residue-field fibre. Thus the given
homomorphism carries this one coordinate torus identically from the chosen
source embedding to the chosen target embedding.

`hasCommonCoordinateMaximalTorus_of_specialFibreIso` proves this property for
a specified homomorphism `f : G → H` between reductive groups over a strictly
Henselian local ring, provided that its special fibre along the quotient
map `Spec(R/𝔪) → Spec R` is an isomorphism. The theorem is quantified in an
arbitrary universe. It needs neither the DVR or domain conditions nor the
fibrewise-isogeny hypothesis used in the later rigidity problem.

The proof first uses the published
`exists_coordinate_fibrewiseMaximalTorus_of_strictHenselian` to choose a
closed coordinate maximal torus in the source. The supporting theorem
`IsReductive.isFibrewiseMaximalTorus_comp_of_specialFibreIso` proves that the
composite is a closed maximal torus in the target: closed immersion follows
from the local special-fibre detection lemma in
`TorusLocalSpecialization.isClosedSubgroup_comp_of_specialFibreIso`;
maximality in the closed fibre follows by transporting the source maximal
torus through the given closed-fibre isomorphism; and maximality in all
residue fibres follows from the published local maximality propagation
theorem. Only the target is required to be reductive in that supporting
transport theorem, because its source torus is already supplied.

Two further lemmas handle the distinction between the quotient residue
field of a local ring and the residue field used by the scheme API.
`isIso_residueFibre_of_fieldPoint` reflects an isomorphism on a supplied
field-valued fibre to the canonical residue-field fibre at its image. Its
proof factors the supplied point through the canonical residue-field map,
compares iterated base change, and reflects invertibility along the ensuing
faithfully flat field extension.
`isIso_closedFibre_of_specialFibre` applies this to the quotient residue map;
its image is the closed point by `IsLocalRing.comap_closedPoint`.

This is an internal composition of the cited published Library lemmas and
the local torus detection module. It supplies the common-torus step of the
prescribed-map rigidity argument in Task 6422. It asserts no finiteness,
centrality, root-data compatibility, or generic-fibre invertibility of the
ambient homomorphism.
