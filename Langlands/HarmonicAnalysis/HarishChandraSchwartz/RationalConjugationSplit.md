# The actual conjugation integral split

This internal unit constructs the truncated open cell and specializes the
Library's generic complex-integral split to actual rational points.
It proves an integral identity from integrability, with no decay assertion.

The generic set `conjugationTruncatedCell hMU A B a` is the image of the
Levi/radical coordinate map `((m,u),v) ↦ m u v⁻¹` on the pairs satisfying
`a (m u m⁻¹) a⁻¹ ∈ A` and `v ∈ B`. If Levi/radical coordinates on the
parabolic are a homeomorphism and the parabolic/opposite-radical map is an
open embedding, their composite is an open embedding.
Consequently the cell is open when both truncation conditions are open.
Injectivity recovers exactly those two conditions from membership of a
coordinate point in the image.

For a connected reductive group over a nonarchimedean local field, choose
any cocharacter `χ`, any compact open subgroup `H`, and any ambient Haar
measure `muG`. The dynamic centralizer, parabolic and radicals are the
actual identity-test subgroups with the published rational-point topology.
The measures on the centralizer and both radicals are the existing Haar
measures normalized on their intersections with `H`.
`rationalDynamicConjugationCell` uses `A = H` and `B = H ∩ V`, where
`V` is the opposite radical. Its openness and coordinate membership
theorems discharge the corresponding set hypotheses of the generic split.

`rationalConjugationPairing_eq_dynamic_split` applies to two functions
bi-invariant under `H` and an integrable conjugation integrand at a point
of the dynamic centralizer. It expresses their actual bilinear pairing as
the integral over the complement of the constructed cell plus the scalar
`rationalDynamicConjugationScalar` times the centralizer integral of the
cuspidal and unipotent factors. The first factor uses the inverse of the
actual positive-radical Haar character; identifying it with the
opposite-radical character is a separate published reciprocity result.

The implemented proof uses
`isHomeomorph_leviUnipotentCoord_rationalPoint`,
`isOpenEmbedding_openCellMap_rationalPoint` and the closed theorem
`rationalDynamicOpenCellConull` for the geometry and null boundary.
Reductive unimodularity supplies ambient right invariance.
The published dynamic radical Haar measures supply inversion invariance.
`isConjModulus_semidirect_closedCharacter` supplies the positive-radical
change of variables, and the inverse character gives the scalar identity
used in the two factors. The function invariances remove the two
truncated radical variables. The generic theorem
`integral_conj_mul_eq_split` then proves the identity.

The scalar uses the explicitly displayed Levi-product parabolic measure;
there is no premise that `H` is stable under the dynamic limit.
The functions need not be Schwartz or cuspidal for this identity.
Convergence remains the precise integrability premise, to be discharged
separately for Schwartz functions by the weighted Xi-square estimate.
