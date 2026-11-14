# Genericity of specialized incident cocharacters

This internal supporting construction transports genericity through the actual
integral split torus of a smooth affine integral model over a local domain.
Genericity means nonzero integer pairing with every actual nonzero adjoint
root. Both the generic field and the full residue fibre are used; the residue
group need not be reductive or connected for this transport.

`IntegralSplitTorusData.isGenericCocharacter_cocharacterSpecialization_iff`
uses the canonical character specialization and its preservation of actual
root membership. In the forward direction each generic root specializes to a
residue root. In the reverse direction each residue root has a unique generic
preimage under the character equivalence. The pairing specialization identity
then transports nonvanishing in each direction.

`IntegralSplitTorusData.genericCocharacterSpecialization` restricts the actual
cocharacter lattice equivalence to the subtypes of generic cocharacters.
Its value formula identifies its forward map with that canonical
specialization, without choosing a different equivalence.

`unramifiedIncidentCocharacter_specialization_isGeneric` applies the generic
transport to the actual torus constructed in a zero-fixer model and the
published `C.incidentFacetCocharacter_isGeneric`. The model's integral points
are the zero subgroup intersected with the pointwise fixer of the supplied
apartment subset. The cocharacter is chosen from a face of a facet of the
maximal unramified building. No extra sign or root-support hypothesis is
supplied by the caller.

For a connected special fibre,
`unramifiedIncidentCocharacter_centralizer_eq_torusCentralizer` applies the
published `IsSplitTorus.dynamicCentralizer_eq_torusCentralizer`, using the
constructed split residue torus, smoothness by base change and the preceding
genericity theorem. This is equality of subgroup functors on all residue
scheme tests.

The provenance is derived from the imported actual-root comparison, lattice
pairing identity, incident-facet cocharacter theorem and generic-centralizer
theorem. These results do not prove radical containment, geometric
parabolicity, reduction preimages or the host statement.
