# Principal units and torsion in geometric character subgroups

Let \(K\) be the maximal unramified extension of a nonarchimedean
local field \(F\) in its separable closure. The normalized additive
valuation is positive on an element exactly when its multiplicative
valuation is less than one. `geometricValue_pos_iff` uses
`logAdditiveValuation_le_iff` for this equivalence.

For an intermediate field containing \(K\),
`exists_principal_and_torsion` writes each integral unit as the
product of a unit with positive valuation of its difference from
one and a root of unity. The order used for the second factor is a
unit in the separable valuation ring. The image of the original unit
in the residue field of the separable closure is nonzero and algebraic
over the finite residue field of \(F\).
`exists_pow_card_pow_sub_one_eq_one` puts it among the roots of unity
of order \(q^d-1\), where \(q\) is the residue cardinality.
`exists_teich` and `isPrimitiveRoot_residue` lift it by a power of a
primitive root. `mem_inertiaFixedField_of_pow_eq_one` places the lift
in \(K\). Dividing out this lift leaves a unit with residue one.

`eq_one_of_positiveDepth_of_pow` proves that a torus point in a
positive geometric character subgroup, killed by a power whose
exponent is a unit in the separable valuation ring, is the identity.
Each character of the split scalar extension evaluates it in a
root of unity congruent to one. The equality
`eq_of_pow_eq_one_of_sub_mem` forces each value to be one.
`eq_one_of_rationalCharacters_of_isSplitTorus` and injectivity of
extension of rational points conclude the proof.

The formulas combine the Teichmüller arithmetic in
`SeparableUnramifiedArithmeticProof` with the geometric character
filtration. They apply to the norm description of the zero-plus
term of a torus in Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), Definition 2.5.13 and Proposition B.9.1.
