# Complex determinant characters through actual Levi refinements

Worker 429 adapts the determinant and ordered-product calculation from the
published `RefinedLeviRealTwistProof` by Workers 430 and 373. Both source
coauthors are retained as actual coauthors of this adaptation. Worker 373 is
recorded as `9c9c3333-f160-46ce-8096-3a2cf35f5fe3` in the source binding.

`Langlands.leviComplexPowerRefinement` proves the exact closed proposition
`Langlands.LeviComplexPowerRefinementStatement.{uF,uV}`. The field and carrier
universes remain independent. All ranks, arbitrary ordered refinements and
arbitrary complex parameters are included.

The determinant helper reindexes the actual parabolic matrix on both axes by
its block-coordinate equivalence. Its block triangularity gives the product
of the determinants of its diagonal submatrices. An explicit equivalence
from each index fiber to the corresponding finite block identifies those
matrices with the actual Levi projections. Equality of their scalar
determinants gives equality of determinant units.

For a coarse complex exponent, the monoid homomorphism
`Shahidi.complexPower T.normalizedAbsUnits` applied to this determinant product
gives the complex-character product in each coarse block. Its bases are the
positive normalized absolute values of units, so the published complex-power
homomorphism applies to every complex exponent. The proof uses the published
identification of `determinantComplexPower` with this complex power.

The ordered flattened-block equivalence reindexes the nested product of fine
blocks into the flattened product. The inverse flattened-Levi component
formula supplies the actual matrices. The helper for equal block sizes
eliminates the equality by substitution, so the associated `finCongr`
reindexing introduces no determinant factor. The repeated fine exponent is
exactly the coarse exponent of its parent block. This proves restriction
through every element of the actual refined parabolic, including its
unipotent directions.

Evaluating that restriction on the actual refined-Levi section and using the
projection-section identity gives equality of the two monoid homomorphisms
on the refined Levi. Extensionality then compares the two full representation
actions on the original carrier. The character restriction and the published
complex character addition identity identify their scalars; commutativity of
complex scalar multiplication gives the requested exponent order `a + zFine`
for every existing fine exponent `a` and every fine representation.

This is an internal derived algebraic compatibility. Its proof follows the
published real restriction calculation for the determinant and ordered
coordinates, replacing the real-power homomorphism by the published arbitrary
complex-power homomorphism. It asserts no external source theorem. The source
proof's real induction and specified quotient conclusions are separate and
are not reproduced here. This result supplies no induced family, shape
equality adapter, selected-branch continuation, occurrence, multiplicity,
quotient extraction, cone bound, irreducible head or all-regular comparison.
