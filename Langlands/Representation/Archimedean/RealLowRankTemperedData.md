# Form and scalar-commutant data in ranks zero and one

This internal support module for Task 7158 states and proves
`RealLowRankTemperedDataStatement`. For every list of real blocks of total
rank at most one, it constructs both
`RealTemperedCommutantReduction.HasTemperedForm` and
`RealTemperedCommutantReduction.HasScalarCommutant` on the actual compact-finite
standard-module space. The equal-exponent hypothesis is unnecessary here.
These are the exact interfaces of the two remaining global prerequisite
statements; their higher-rank cases remain open.

The rank-zero and rank-one modules supply complex linear evaluation
equivalences `e` with `ℂ`. Any complex linear endomorphism of such a space is
scalar: write every `v` as `e(v) • e⁻¹(1)` and apply linearity. This proves
the scalar-commutant property independently of the actions.

The form is explicitly `B(v,w) = e(v) * conj(e(w))`, linear in the first
argument and conjugate-linear in the second. It is diagonally anisotropic,
and the equivalence supplies nontriviality. In rank zero the compact action
is trivial. In rank one the principal-series law says that the compact
action in evaluation coordinates is multiplication by `d.character(det k)`.
An orthogonal matrix has determinant `1` or `-1`; the prescribed signed-power
formula of the real character gives absolute value one on either value.
These facts prove compact invariance of the form.

Every real infinitesimal operator is a complex linear endomorphism and
therefore acts by a scalar `c`. Its two form contributions are consequently
`c B(v,w)` and `conj(c) B(v,w)`, so their sum is
`(c + conj(c)) B(v,w)`, exactly the scalar identity the interface requires.
No derivative computation or exponent restriction is needed for this
one-dimensional argument.

The final theorem uses positivity of block ranks to identify the rank-zero
list with the empty list and the rank-one list with a singleton real
character. The whole construction is derived from Library definitions and
the explicit low-rank evaluation equivalences. It uses no higher-rank
irreducibility, Langlands quotient or classification theorem.

Two final implications, `realTemperedForm_of_rank_ge_two` and
`realTemperedScalarCommutant_of_rank_ge_two`, reduce each complete global
prerequisite to the same prerequisite in ranks at least two. They split on
whether the rank is at most one and use the proved low-rank theorem in that
case. All original block, rank and equal-exponent inputs remain present.
