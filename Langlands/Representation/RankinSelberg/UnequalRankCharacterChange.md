# Conditional rational unequal-rank character transport

This internal construction continues the explicit change of variables in
`UnequalRankCharacterIntegrals`. It reuses `EqualRankCharacterChange` for the
integer spectral-power normalization and `LaurentTransport` for multiplication
of rational continuations and Laurent spans. It adds no original-literature
assertion and does not prove either canonical Haar measure law or existence of
analytic continuations or normalized generators.

Let the smaller rank be `n+1`, the gap be `d=j+k+1`, and the larger rank be
`n+d+1`. All three indices may be zero. Write `D(s)` for the determinant weight
of the smaller character-change diagonal `d_a`, `cq` for its quotient modulus,
and `cr` for the rectangular modulus. The corrected large function is
`W_new(g)=W(D_a g R⁻¹)` from `UnequalRankCharacterTransport`; the smaller inverse
character function is `W'_new(g)=W'(d_a g)`.

The integral theorem imported from `UnequalRankCharacterIntegrals` states

`D(s-d/2) I_new(s) = cq cr I_old(s)`.

The half-gap is computed in the complex numbers, after casting the natural gap.
For positive natural `q`, assume explicitly that
`|det d_a| = q^(-e)` with integer `e`. With `X(s)=q^(-s)`, the new
`determinantWeight_shift_eq_spectralPoint_zpow` proves

`D(s+t) = X(s)^e D(t)`.

Its proof uses complex-power additivity at the nonzero absolute determinant,
followed by the published integer-power normalization lemma. In particular,
`A=D(-d/2)` is nonzero. `unequalRankCharacterChangeScalar` is the actual complex
unit `c=cq cr/A`, and `unequalRankCharacterChangeLaurentUnit` is the actual
Laurent unit `c X^(-e)`. Both Jacobian factors and the half-gap constant are
retained; the constant is not merely the equal-rank quotient modulus.

The forward and reverse integral lemmas solve the imported identity using the
nonzero factors. They give

`I_new(s) = c X(s)^(-e) I_old(s)` and
`I_old(s) = c⁻¹ X(s)^e I_new(s)`.

These are identities of the actual iterated total complex Bochner integrals.
They require the two explicit measure laws but no integrability or S-finiteness
hypotheses. The continuation lemmas multiply an already supplied rational
continuation by `C(c) X^(-e)` or its reciprocal. They preserve a right-half-plane
agreement and nonvanishing of the rational denominator through the published
Laurent continuation API; they do not create continuations without a witness.

For the intrinsic zeta-value sets, both measures are required to be S-finite.
The forward proof transports actual coefficient functions through the exact
Whittaker-set image equality and uses the existing product-convergence
equivalence with the same half-plane bound. The reverse proof first recovers
source coefficient witnesses through that image equality, then transports
convergence and continuation back. Thus neither direction replaces the
representation's coefficient functions by arbitrary Whittaker functions.
The representations are arbitrary algebraic complex representations; no
smoothness, irreducibility, genericity, central character or multiplicity-one
hypothesis is needed for these conditional consequences.

`zetaSpan_unequalRank_characterChange` applies the Laurent-unit transport lemma
to those two directions. It proves equality of the existing intrinsic Laurent
submodules. `isUnequalRankLPolynomial_characterChange` consequently identifies
the normalized polynomial-generator relations for each polynomial, and
`normalizedGeneratorExists_unequalRank_characterChange` transfers existence
and uniqueness as an equivalence. These results do not assert either side of
that existence equivalence.

Finally, the two `_normalized` wrappers install the topology, valuation,
local-field and Borel structures from the supplied p-adic `TopologicalData`.
They use its actual residue cardinality and determinant order, with
`normalizedAbs_of_ne_zero` supplying the numerical power law. They still
require both S-finite measures and both explicit measure-scaling laws, and
respectively conclude Laurent-span equality and normalized L-polynomial
relation equivalence. The shared canonical quotient statement and the
rectangular Haar Jacobian remain separate proof obligations.
