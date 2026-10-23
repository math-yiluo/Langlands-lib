# Finite local denominator values in the total idele invariant

This is a derived construction for Galois extensions of number fields in an
arbitrary common universe. It uses the supplied local invariant family `I`,
assuming its `RelativeImages` property, and explicit choices of finite and
infinite places above the base places.

`localDenominatorToTotalInvariantRange` includes the denominator subgroup for
the completed degree at a chosen finite place into the range of
`totalIdeleInvariant`. Its underlying map is the inclusion into the rational
numbers modulo the integers. The witness for membership in the range is
`finiteIdeleInvariantLift`, already constructed in `IdeleFiniteSection`.

The auxiliary lemmas establish that this witness has the required total
invariant. A single finite-coordinate idele has every infinite coordinate
equal to one. Galois transport preserves this property, so the coset sum
defining `ideleSemilocalSection` has every infinite coordinate zero in the
additive coefficient representation. Representing the inverse Shapiro image
by a two-cocycle and mapping its coefficients through that section gives a
representative with infinite adele part one. The published criterion
`archimedeanIdeleInvariant_eq_zero_iff` then proves that
`ideleLocalSection` has zero invariant at every infinite place.

Consequently, the total invariant on this section equals its finite invariant
sum. The evaluation theorem from `IdeleFiniteSection` reduces that sum to the
chosen local invariant, and the inverse local invariant equivalence gives the
prescribed denominator value. The final coercion lemma records that the new
range map sends each value to itself.

The provenance is internal: the construction combines the published finite
section, archimedean cocycle criterion, and total invariant. No reciprocity
law is assumed or proved here. The denominator is the local completed degree;
the module does not assert that this degree equals the global degree, nor
that the total invariant descends to all idele-class cohomology.
