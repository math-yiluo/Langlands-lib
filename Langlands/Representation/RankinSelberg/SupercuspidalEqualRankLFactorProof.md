# Equal-rank supercuspidal L-polynomial

`supercuspidalEqualRankLFactor` proves the unchanged proposition
`SupercuspidalEqualRankLFactorStatement.{uF,uV,uW}`. It gives the normalized
L-polynomial as the finite product of `1 - a X`, where the parameters are exactly
`a = q^(-u)` for which the twist of the first representation by
`|det|^(-u)` is equivalent to the smooth contragredient of the second.
The field and both representation carriers have independent universes.
This is the target's contragredient convention for JPSS 1983, Proposition
(8.1)(ii), printed page 443, as corrected by Henniart 2002, section 3.3,
printed page 598.

The implementation first obtains a nonzero standard Whittaker functional for
the irreducible supercuspidal first representation from the proved
supercuspidal Kirillov theorem. Whittaker multiplicity one gives full
Whittaker type. The supplied standard Whittaker type of the second
representation is transported to inverse Whittaker type and yields a nonzero
inverse functional. The canonical quotient Haar measure is compatible with
the group and unipotent Haar measures. The equal-rank analytic theorem
therefore supplies the analytic conclusion for these fixed functionals.
The symmetric L-polynomial existence theorem provides an intrinsic
L-polynomial, and the analytic bridge identifies it with the normalized
generator of the actual rational integral values. These steps discharge the
functional, measure, analytic and polynomial-existence inputs of the helpers.

The central-binomial denominator bound, applied with the proved Kirillov
theorem, shows that this normalized polynomial is separable. Its constant
coefficient is one. The finite set used in the conclusion is
`reciprocalRootParameters P`: the inverses of the distinct complex roots of
this polynomial. Its membership criterion is precisely that `a` is nonzero
and `P(a⁻¹) = 0`.

For such a reciprocal root, the complex logarithm supplies `u` with
`a = q^(-u)`, using `q > 1`. The polynomial root is thus `q^u`.
`exists_contragredient_twist_of_supercuspidal_root` supplies the required
field-unit character and the equivalence with the smooth contragredient.
That theorem uses the nonzero denominator-cleared Laurent residue, its
vanishing on row tests of value zero at the origin, and descent to a
nonzero covariant bilinear pairing.

For the reverse membership implication, the stipulated values of the supplied
field-unit character identify its determinant composite with the canonical
determinant complex-power character at `-u`.
`supercuspidal_root_of_contragredient_twist` then forces a root at `q^u`.
Its proof uses a compact central row shell with a convergent positive
integral, multiplicity-one transport to the prescribed second functional,
and the actual central translation identity. Assuming regularity at the
twist point forces that positive integral to vanish. The theorem is applied
here with the proved Kirillov statement, the inverse Whittaker type,
the canonical compatible quotient measure, and the analytic conclusion and
normalized generator already constructed.

Finally, `eq_prod_reciprocalRootParameters` recovers the normalized polynomial
from its reciprocal roots. Separability ensures that each factor occurs
once, and the constant coefficient one fixes its scalar. Replacing the
intrinsic L-polynomial by this equal finite product gives the required
`IsPadicPairLPolynomial`. Every intermediate premise is discharged in the
final theorem.
