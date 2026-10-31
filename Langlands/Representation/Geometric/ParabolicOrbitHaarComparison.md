# Actual orbit Haar characters and Levi factorization

This internal normalization prerequisite uses the actual intermediate group
`parabolicOrbitStagesQuotient`, the target radical, and the correction subgroup
`V_C ∩ w P_B w⁻¹`. It is uniform in the commutative topological ring and block
shapes wherever the indicated local compactness and separation hypotheses
suffice; the last two theorems specialize to every actual finite p-adic
extension with its supplied compatible topology.

`parabolicOrbitStagesAmbient` sends an intermediate element to its actual
matrix in the intersection of the target Levi and the conjugated source
parabolic. The two normalizer maps use this matrix to act on the target radical
and the correction subgroup. Both maps are continuous for the inherited
topologies.

`parabolicOrbitStagesCorrectionModulus` is the actual closed-subgroup Haar
character of the correction action. `parabolicOrbitStagesHaarRatio` is the
target radical character divided by the correction character. These are
definitions of actual Haar characters, with no supplied scaling equality.
The nested kernel's inverse conjugation is intertwined by the published
ambient equivalence with inverse conjugation by the same matrix. The theorem
`parabolicOrbitNestedKernel_haarChar` therefore identifies its Haar character
with the inverse of the ambient radical character.

For a p-adic realization, `parabolicOrbitStagesRadicalModulus` proves that the
ambient radical character is exactly the explicit block modulus
`T.leviModulus C l.val`. The proof transports to the intrinsic radical using
the published `unipotentRadicalAmbientEquiv`, identifies conjugation with the
published Levi action, and applies `glBlockModulusHaar`. Haar scalar uniqueness
then identifies the character, including its inverse-pushforward convention.
There is no assumption that a Haar measure has finite total mass.

`parabolicOrbitStagesCorrectionModulus_factor` proves that the correction
character is unchanged when the intermediate element is projected to the
supplied target refined Levi and included again. The full target intersection
refinement is retained. The correction character is continuous because its
kernel is open. Transport to the actual refined parabolic permits direct use
of `refinedPositiveCharacter_factor`; the continuous and algebraic subgroup
equivalences agree on underlying elements.

All constructions and proofs are internal consequences of the imported
subgroup, Haar-transport, explicit block-scaling and positive-character
results. This pair supplies a prerequisite for normalization cancellation.
It does not assert the full scalar cancellation, integral equivalence or
natural normalized Jacquet comparison.
