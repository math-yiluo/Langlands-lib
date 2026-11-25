# Opposite factors over a Henselian discrete valuation ring

This internal helper proves
`IntegralTorusData.integral_oppositeFactors_of_not_mem_positivePoints` over a
Henselian discrete valuation ring with perfect residue field and its specified
fraction field. The ambient generic group is connected reductive, its specified
torus is maximal split, the neutral integral model is smooth with connected
fibres, and the supplied compatible integral torus is split. For any nonidentity
integral root point outside the actual radical preimage, both factors of every
prescribed normalizing opposite-factor pair are integral.

`HenselianIntegralOppositeFactorsStatement` packages this assertion with all
base rings, fraction fields, models, tori, quotients, roots, points and ordered
pairs universally quantified. The theorem `henselianIntegralOppositeFactors`
proves that proposition. It is the general-base sufficiency interface consumed
by the unramified positive-reduction proof, where the base ring is the actual
maximal-unramified valuation ring.

The proof adapts the sufficiency argument of
`IntegralOppositeFactorsProof` from local-field integers to this general base.
The closedness of the integral torus is derived using
`IntegralModel.isClosedSubgroup_of_split_generic`. Henselian specialization
makes its residue torus maximal split, and the perfect-field unipotent quotient
theorem gives maximality of the same torus in the supplied reductive quotient.

An integral section representing the root point has nonidentity quotient
reduction: identity reduction would place the section in the full radical
preimage by the actual fppf quotient's full-kernel equality. The character,
root membership and complete prescribed opposite-pair predicate transport
through the specified generic torus isomorphism. A positively pairing generic
cocharacter lifts through the same split integral torus; compatibility and
base-change invariance prove positive integral pairing.

The relative-root-system theorem and the quotient predicate supply the remaining
inputs to `IntegralModel.integral_oppositeFactors_of_residueQuotient`. That
theorem constructs the requisite centralizer and action data internally and
returns integrality of the original ordered pair. This helper introduces no
local-field assumption, extra quotient action, or reflection-lifting premise.
Its provenance is internal composition of the imported results.
