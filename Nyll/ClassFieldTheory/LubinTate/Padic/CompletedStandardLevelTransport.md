# From the finite standard p-adic Lubin–Tate level to the completed level

Module `Nyll.ClassFieldTheory.LubinTate.Padic.CompletedStandardLevelTransport`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a prime `p` and a level `n`, the finite standard Lubin–Tate level over ℚ_p for the uniformizer `p` embeds over ℚ_p into the completed level `padicCompletedLevelField p n` by `padicStandardLevelEmbedding p n`, which sends the primitive generator to the chosen completed primitive point. This file shows that the embedding respects valuation rings, topology and the analytic action of p-adic units, and fixes which unit indexes which automorphism, before the completed Frobenius is used in the changed-uniformizer norm argument.

## Main definitions and results

- `padicStandardLevelIntegerEmbedding`: the embedding restricted to valuation rings. It agrees with the field embedding (`_coe`), sends the finite primitive point to the completed one (`_apply_primitivePoint`), is continuous for the two maximal-ideal-adic topologies (`_continuous`) and is compatible with the maps from the p-adic integers (`_comp_coefficientHom`).
- `padicCompletedLevelPowerSeriesEval_map_padicCoefficients` and `padicStandardLevelIntegerEmbedding_powerSeriesEval`: for a point `x` of the finite valuation ring with `PowerSeries.HasEval x`, evaluating a power series over the valuation ring of ℚ_p at `x` and then embedding is the same as evaluating at the image of `x`, in the completed level, the series with coefficients pushed to the Witt ring; at any such point of the completed valuation ring, the latter equals evaluation through the direct coefficient map from the valuation ring of ℚ_p.
- `padicStandardLevelIntegerEmbedding_apply_primitivePointUnitAction`: the embedding carries the finite action of a unit `u` on the primitive point to the completed action `padicCompletedStandardPrimitivePointUnitAction p n u` with the same `u`.
- `padicStandardUnitParameterLevelRoot_class` and `padicCompletedStandardPrimitivePointUnitAction_eq_unitParameterRoot`: the action of `u` is the root attached to the unit-parameter class `standardLubinTateUnitParameterClass` of `u`, at the finite and at the completed level.
- `padicCompletedUnitFrobeniusLiftEquiv_standardLevelEmbedding`: on the image of the finite level, the completed Frobenius lift indexed by `u` restricts to the finite automorphism `standardLubinTateUnitParameterAlgEquiv` of the class of `u`; `_symm_standardLevelEmbedding` gives the inverses.
- `padicCompletedInverseUnitFrobeniusLiftEquiv_standardLevelEmbedding`: the inverse of the lift indexed by `u⁻¹` acts on the finite level by the automorphism of the class of `u`.

## Proofs

The integral embedding exists because both valuation rings are integral closures (of the valuation ring of ℚ_p and of the completed unramified ring), and an element integral over the first maps to one integral over the second. The Frobenius statement is checked on the generator of the power basis of the finite level.

## Points to watch

- Everything is for the single uniformizer `p` of ℚ_p and the standard Lubin–Tate series.
- The orientation matters: the lift indexed by `u` acts by the class of `u`, so its inverse acts by the class of `u⁻¹`; the last theorem, the form the file names as the one used for the local Artin map after changed-uniformizer descent, uses `u⁻¹`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/Padic/CompletedStandardLevelTransport.lean`: the Lean file is the source byte for byte (SHA-256 `fa0178e245b738e2f3aa478f007b03fae7d7b6b0634b7c3bfa84389a7c060757`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
