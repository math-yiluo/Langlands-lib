# The spherical L-factor generation facts, one field at a time

Module `Langlands.Representation.Conductor.SphericalLFactorGenerationFieldReduction`,
namespace `Langlands.Conductor`.

## Contents

- `SphericalLFactorGenerationAt F`: the published `SphericalLFactorGenerationStatement` for
  one nonarchimedean local field `F`, given by its instances; the binders after the field
  and the conclusion are copied verbatim. `sphericalLFactorGenerationStatement_iff` and
  `padicSphericalLFactorGenerationStatement_iff` (with the canonical structures of a
  p-adic field) hold by `Iff.rfl`.
- `generation_of_orderedAt`: clause 3 of the statement for norm-ordered parameters `x`,
  from Jacquet's Lemma 3 for `x` at the field of `π`. It is the published
  `generation_of_ordered` (module `SphericalLFactorGenerationReduction`) with the
  hypothesis specialized to the given data: Jacquet's Lemmas 1 and 2 (published
  `orderedUnramifiedSphericalCyclicity`, `orderedUnramifiedWhittakerRealization`) and the
  published `isSphericalIntegralSpan_of_model`.
- `sphericalLFactorGenerationAt_of_generationAt F hgen`: `SphericalLFactorGenerationAt F`
  from `OrderedUnramifiedCorankOneGenerationAt F`. The proof is that of the published
  `sphericalLFactorGeneration_of_ordered`, with the published proofs
  `sphericalCorankOneConvergence` and `unramifiedCorankOneLaurent` (which hold over every
  field) for clauses 1 and 2, and `generation_of_orderedAt` for clause 3, after sorting
  `x` by norm.
- `sphericalLFactorGeneration_of_generationAt`: `SphericalLFactorGenerationStatement` from
  Jacquet's Lemma 3 at every nonarchimedean local field.

With `orderedUnramifiedCorankOneGeneration_of_premises` (module
`OrderedUnramifiedGenerationFromPremises`), the general statement follows from the three
premises of `AllField.Representation.RankinSelberg.TemperedTypePremisesStatement` at every
nonarchimedean local field. The Library proves them over p-adic fields.

Source: Jacquet 2012 (literature ID `jacquet-2012-conductor-correction`), section 1,
printed pages 517–519.
