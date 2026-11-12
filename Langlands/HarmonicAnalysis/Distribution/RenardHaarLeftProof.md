# Left Haar distributions in the full algebraic dual

This module proves the exact `LeftHaarStatement` and
`MeasureHaarBridgeStatement` at the full group universe through `leftHaar`
and `measureHaarBridge`. It imports the published finite expansion proof
`Hecke.RenardTestDecomposition.rightInvariantExpansion`.

The proof compares invariant algebraic functionals on finite compact-open
coset expansions. Fix a positive reference distribution and a compact-open
subgroup indicator. For any test, choose a common compact-open invariance level
for that test and the reference indicator. Each finite right-invariant
expansion is a sum of left translates of the level subgroup indicator.
Consequently the same coefficient sum computes the value of every
left-invariant algebraic functional. Positivity of the reference distribution
ensures the coefficient sum for the reference indicator is nonzero. Division
then gives a single scalar working on every test, with uniqueness determined
by the nonzero reference value. This classifies the full algebraic dual without
any continuity, measure representation or countability premise.

More precisely, `invariant_value_of_rightInvariant` obtains the coefficient sum
once and proves its value formula simultaneously for every invariant
distribution. `leftInvariant_scalar_unique` chooses a reference subgroup
indicator `φ₀` and the scalar `S(φ₀)/T(φ₀)`. A common compact-open level for
`φ₀` and an arbitrary test gives a nonzero reference coefficient sum and proves
that this same scalar works on that test. Evaluation at `φ₀` proves scalar
uniqueness. The zero functional is included among the distributions `S`.

The actual Mathlib Haar integration functional supplies positivity and left
invariance via the preceding density proof unit. It therefore realizes the
left Haar distribution and compares with every left-invariant algebraic
distribution. For existence without a supplied measurable structure, the proof
uses the Borel measurable space and Mathlib's `Measure.haar`. No supplied
topology or algebraic distribution carrier is replaced.

The auxiliary `measureHaarBridge_of_expansion` and `leftHaar_of_expansion`
isolate the finite expansion input. The final two declarations supply its
published proof, so the exported existence and comparison assertions have no
remaining expansion premise.

The finite expansion and common-invariance steps implement the argument of
Renard II.3.6, printed pp.46–47 / PDF pp.52–53; existence is supplied by
Mathlib's actual Haar measure rather than a fresh compatible-family
construction. Source: David Renard, *Représentations des groupes réductifs
p-adiques*, French version of 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`.
