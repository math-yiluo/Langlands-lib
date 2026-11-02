# Conditional certified factor separation

The closed theorem
`Langlands.Global.FactorSeparation.certifiedFactorSeparation` proves the
existing `CertifiedFactorSeparationStatement` for every prime, prime instance
and p-adic field, with independent field, parameter, automorphic and
epsilon-system universe parameters `uF`, `uP`, `uA`, `uE`. It applies the
published full conjunction `Langlands.Global.gammaSeparation`. The helper
`certifiedFactorSeparation_of_separation` makes that dependency explicit; the
closed theorem has no additional separation premise. The statement pair and
its imported pairs are unchanged.

The proof unpacks the arithmetic and automorphic common-gamma certificates.
At each supplied self-dual measure, the automorphic certificate supplies smooth
dual classes, original and dual L-polynomials `Q`, `Qd`, and an epsilon pair
`e`. The arithmetic certificate supplies a unit `a`, integer `m` and their
epsilon certificate for the fixed system.

The tensor-class equality and the existing
`WeilDeligne.rationalLRatioClass_classOf` and `rationalLRatio_eq` identities
express the arithmetic ratio using the actual tensor determinant polynomial
`P` and its actual dual determinant polynomial `Pd`. The residue reflection
is exactly `q⁻¹ X⁻¹`, where the canonical residue cardinality satisfies `q > 1`.
Both gamma certificates thus give the same rational expression:

\[
 aX^m\,\frac{P(X)}{Pd(q^{-1}X^{-1})}
 = e_1X^{e_2}\,\frac{Q(X)}{Qd(q^{-1}X^{-1})}.
\]

The actual Euler polynomials have constant coefficient one. The published
`IsAutomorphicPairLPolynomial.coeff_zero` gives the same normalization for
`Q` and `Qd`. The arithmetic no-common-root premise applies to `P`, `Pd`;
the certified automorphic premise is specialized to the supplied measure,
dual classes and polynomials. The four-polynomial component of
`GammaSeparationStatement` then identifies `P = Q`, `Pd = Qd` and the two
rational epsilon monomials. Both root conditions are used as supplied
hypotheses.

Equality of rational epsilon monomials is evaluated at every nonzero complex
number using `RankinSelberg.eval_rationalEpsilonMonomial`. The complement of
zero is infinite, so `RankinSelberg.unitMonomial_eq_of_infinite` identifies
both the unit coefficient and the integer exponent. Rewriting the original
arithmetic epsilon certificate supplies the same pair `e` as the unchanged
automorphic certificate. Finally, the tensor-class equality and polynomial
identities rewrite both reciprocal rational L-factors. The proof retains the
original self-dual measure existence witness and works at every self-dual
measure; it evaluates only the epsilon monomials at nonzero points.

The motivating source is Guy Henniart, *On the local Langlands conjecture for
GL(n): the cyclic case*, Annals of Mathematics (2) 123 (1986), 145–203,
section 4.4, lemma and proof, printed page 159 / PDF page 16, registered as
`henniart-1986-cyclic`. The certificate and independent-universe adapter is
derived internal content. The arithmetic epsilon system and its certificate,
additive character, actual tensor representative, smooth dual classes and all
factor certificates remain fixed. The result supplies no global functional
equations, actual pole-region hypotheses, factor or measure existence theorem,
or unconditional `AssociatedFactorStatement`.
