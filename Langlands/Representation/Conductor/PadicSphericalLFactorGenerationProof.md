# The spherical L-factor generation facts over p-adic fields

Module `Langlands.Representation.Conductor.PadicSphericalLFactorGenerationProof`.

`Langlands.Conductor.padicSphericalLFactorGeneration` proves
`Langlands.Conductor.PadicSphericalLFactorGenerationStatement.{uF, uV}`
([`PadicSphericalLFactorGenerationStatement`](PadicSphericalLFactorGenerationStatement.md))
exactly, with no additional premises. Its axioms are `propext`, `Classical.choice` and
`Quot.sound`.

## Proof

For a prime `p` and a p-adic field `K`, the statement is
`SphericalLFactorGenerationAt K.Carrier` with the canonical structures
(`padicSphericalLFactorGenerationStatement_iff`). The field-by-field reduction
`sphericalLFactorGenerationAt_of_generationAt`
([`SphericalLFactorGenerationFieldReduction`](SphericalLFactorGenerationFieldReduction.md))
derives it from Jacquet's Lemma 3 at `K.Carrier`, which is
`padicOrderedUnramifiedCorankOneGeneration p K`
([`PadicOrderedUnramifiedCorankOneGenerationProof`](PadicOrderedUnramifiedCorankOneGenerationProof.md)).
The reduction uses the published proofs of convergence, of the Laurent clause and of
Jacquet's Lemmas 1 and 2, which hold over every nonarchimedean local field.

Source: Jacquet 2012 (literature ID `jacquet-2012-conductor-correction`), section 1,
printed pages 517–519.
