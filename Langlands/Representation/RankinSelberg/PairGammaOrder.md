# Spectral orders from Rankin–Selberg denominator polynomials

`meromorphicOrderAt_eval_spectralPoint` identifies the meromorphic order of
`s ↦ P(q^(-s))` at any complex point with the root multiplicity of its
nonzero polynomial `P` at the corresponding spectral parameter. Factor `P`
by the maximal power of the associated linear polynomial. The remaining
factor is analytic and nonzero there. Evaluating at `q^(-s)` preserves order
because this exponential has nonzero derivative for `q > 1`.

`meromorphicOrderAt_rationalGammaExpression` then computes the order of the
rational gamma expression. The forward L-denominator contributes positively
at `q^(-s)` and the reflected L-denominator contributes negatively at
`q^(-(1-s))`. The epsilon monomial is an analytic unit. This calculation uses
the equality of punctured germs for the gamma expression, including at
points where the displayed numerator and denominator both vanish.

`SupercuspidalOfSelfPairGammaOrderStatement` uses this identity for a generic
unitarizable representation and its actual smooth contragredient. The
certified self-pair gamma is assumed to have order one at zero and only
nonpositive order at other real points. The proof uses the reflected
inverse-transpose pair at `s = 1`. Its members are generic and unitarizable,
and the p-adic case of Getz–Hahn (2024), Theorem 11.5.2, printed p. 305
(PDF p. 316), makes its reflected L-denominator nonzero there. The order-one
condition therefore gives a simple root of the forward L-denominator at
one. The local criterion in `SelfPairSupercuspidality` gives
supercuspidality.

This is derived content. The gamma expression is the local
Rankin–Selberg convention used in Henniart (2000), Appendix A.1–A.3,
printed pp. 453–454 (PDF pp. 15–16). The final simple-order criterion
also uses the diagonal pole calculation of Jacquet–Piatetski-Shapiro–Shalika
(1983), Proposition (8.1)(ii), printed p. 443 (PDF p. 78), and the product
formula of Proposition (8.4), printed pp. 451–452 (PDF pp. 86–87).
