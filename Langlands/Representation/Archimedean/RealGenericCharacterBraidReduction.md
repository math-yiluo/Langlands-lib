# Conditional polynomial-to-generic braid comparison

This derived internal module proves the actual integral generic character braid
when either parameter is one or two. It also proves a reduction from a full
normalized compact polynomial braid to the actual generic braid throughout
the two positive real half planes. The full polynomial identity remains an
explicit premise in that second conclusion.

`PolynomialBraid N n m` is the displayed identity in the endomorphisms of
`degreeLE 3 N`:

`P_n(-i X) P_(n+m)(-i Y) P_m(-i X)
 = P_m(-i Y) P_(n+m)(-i X) P_n(-i Y)`,

where `X` and `Y` are the actual adjacent compact rotation generators at
positions zero and one. `P_ell` is the existing tail polynomial.

`IntegralParameters a b c n m` requires positive natural `n,m` and the two
generic parity conditions `n ≡ pairParity a b` and
`m ≡ pairParity b c`. `middle_parity` derives the generic parity for
`n+m` and `pairParity a c`.

`inverse0` and `inverse1` are the actual reciprocal generic Frobenius crossings.
Their compact operators are
`P_ell(eps)^(-1) • P_ell(-i gen)`, as proved in
`RealGenericCompactCharacter.inverse_integral_action`. Their mutual inverse
laws with `swap0` and `swap1` are actual identities on the appropriate
character spaces.

`inverseLeftWord` reverses the three crossings of the actual generic left
word; `inverseRightWord` does the same for the right word. Both go from
`[c,b,a]` to `[a,b,c]`. Their exact fixed-degree compact actions are proved.
The two products have the same three scalar normalization factors. Given
`PolynomialBraid N n m`, commutativity of these complex scalars therefore
gives equality of their compact operators. Choosing a degree for each actual
input and using principal-series restriction injectivity proves equality of
the two actual inverse words (`inverseWords_eq`).

The proof then uses the mutual inverse laws: the inverse left word composed
with the generic left word is the identity, and the generic right word
composed with its inverse word is the identity. Equality of the inverse words
therefore gives `integral_braid`. This uses polynomial identities on actual
parity models and never asserts that a polynomial operator is invertible
on the whole compact degree space.

For `n` or `m` equal to one or two, `polynomial_braid_small` applies the proved
normalized compact polynomial braid and the actual compact generator
relations. Thus `integral_braid_small` is unconditional on any full braid
premise.

For the second conclusion, assume `PolynomialBraid N n m` for every
`N,n,m`. Every parameter pair in the positive integral parity grid has
positive natural coordinates satisfying `IntegralParameters`. The proved
integral comparison gives the actual grid equality
(`grid_braid_of_polynomial`). Applying the previously proved actual
rational-family extension then proves `generic_braid_of_polynomial` for
all complex parameter pairs whose coordinates have positive real part.
The character data and their exponents stay fixed throughout; the variable
maps are compact-equivariant Frobenius maps, with no assertion that every
parameter satisfies the Lie recurrence of the fixed exponent list.

`RealGenericCharacterBraidReductionStatement` packages the unconditional
small integral cases and this conditional full generic conclusion.
`realGenericCharacterBraidReduction` proves it.

The provenance is the explicit reciprocal multiplier, actual Frobenius inverse
laws, finite compact realization, proved small compact braid, and rational
grid extension. The compact polynomial braid used for the small cases is
`RealDifferentialCharacterBraid.normalized_braid_small`. The full polynomial
premise is proved in `RealCompactCharacterPolynomialBraid.polynomial_braid`;
degeneration to canonical tails at poles, compatibility with the chosen
interlaced equivalence and the filtration kernel-image containments are not
proved in this module.
