# Descent from prime-power local degree coverage

This module constructs a conditional additive equivalence on the actual
idele-class degree-two cohomology of a Galois extension `E/F` of number
fields in an arbitrary common universe. The local invariant family `I` is
supplied, with its `RelativeImages` property. The finite and infinite lifts
`wf` and `wi` are explicit choices of places above the places of `F`.

Write `n = Module.finrank F E`. The proposition
`PrimePowerLocalDegreeCoverage wf` says that for every prime `p` and positive
integer `k`, if `p ^ k` divides `n`, some finite place `v` of `F` has selected
completed extension degree divisible by `p ^ k`. The completion algebra is
the existing scoped `FiniteExtension` algebra, using the chosen place's
lies-over witness. The place `v` may depend on `p` and `k`; the condition
does not require one place whose local degree is `n`.

The theorem `totalIdeleInvariant_range_of_primePowerLocalDegreeCoverage`
shows that this coverage condition makes the range of the total idele
invariant equal to `denominatorSubgroup n`. Its proof first uses the existing
global denominator bound to include the range in that subgroup. The
subgroup is finite of cardinality `n`, by `denominatorEquiv`, and therefore
the range is finite. At each finite place, the published local section
induces `localDenominatorToTotalInvariantRange`, an injective additive map
from the local denominator subgroup to the total invariant's range.
Lagrange divisibility and the cardinality of that local denominator subgroup
show that the local degree divides the range cardinality. Coverage and
`Nat.dvd_iff_prime_pow_dvd_dvd` then imply that `n` divides the range
cardinality. The range is a nonempty finite subgroup, so its cardinality is
positive. Its inclusion into the subgroup of cardinality `n` must consequently
be an equality. This argument also covers `n = 1`, for which the coverage
condition is vacuous. The next theorem expresses the range equality as
surjectivity of `totalIdeleInvariantToDenominator`.

The definition `ideleClassInvariantEquivOfPrimePowerLocalDegreeCoverage`
additionally assumes reciprocity `Reciprocity.SumOfInvariantsVanishes I x`
for every field-unit cohomology class `x`, an explicit `Finite` instance for
`relativeIdeleClassCohomology F E 2`, and the bound
`Nat.card (relativeIdeleClassCohomology F E 2) ≤ n`. It returns an additive
equivalence from that actual idele-class cohomology group to
`denominatorSubgroup n`. Reciprocity supplies the kernel inclusion for the
actual quotient cohomology map; the preceding surjectivity theorem and the
order bound supply the other inputs to `FiniteInvariantDescent.equiv`.
The evaluation theorem proves that the equivalence sends the quotient of
an idele cohomology class to its denominator-valued total invariant. The
last theorem proves that the actual quotient cohomology map is surjective
under the same hypotheses.

This is an internal derivation from `IdeleTotalSection`,
`IdeleInvariantDenominator`, `IdeleInvariantDescent`,
`FiniteInvariantDescent`, and Mathlib's prime-power divisibility and finite
subgroup cardinality results. It broadens the published full-local-degree
construction while leaving that construction unchanged. No arithmetic
existence theorem is invoked to discharge coverage. Coverage, reciprocity,
finiteness, and the order bound remain unproved hypotheses here, even when
`E/F` is cyclic. This module neither supplies a global family nor proves
`GlobalInvariantStatement` or its restriction, inflation, and local laws.
