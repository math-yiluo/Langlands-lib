# Products of rational-value families

This internal algebraic development supports the product-generator step in
Godement–Jacquet analytic induction. It uses the published
`Langlands.RankinSelberg.RationalZeta` definitions without changing them.
`productRationalValues A B` consists of the products `a * b` with `a ∈ A`
and `b ∈ B`, in the rational function field over the complex numbers.

`zetaSpan_productRationalValues` is Mathlib's product-of-spans theorem applied
over the actual Laurent coefficient ring. Consequently,
`normalizedGenerator_productRationalValues` proves that normalized generators
`P` and `Q` for the two value families give the normalized generator `P * Q`
for their products. The constant coefficient is one by the constant-coefficient
formula for a polynomial product. The span equality follows from the product
of the two singleton reciprocal spans and the inverse-of-product identity in
the rational function field. This proves both span inclusions.

`normalizedGenerator_of_span_eq` transports the normalized generator across
an equality of Laurent spans. `normalizedGenerator_twoBlock_of_span_eq`
combines these facts for the ordered index set `Fin 2`, retaining the displayed
polynomial product over that index set.

These are derived algebraic lemmas, rather than translations of an additional
source statement. The analytic motivation is the finite product expansion and
reverse generation in Godement–Jacquet, *Zeta Functions of Simple Algebras*
(1972), Theorem 3.4, printed pages 40–45. This module does not prove either
analytic step: an application to actual induced integrals must separately
prove the equality of their Laurent span with the product of block spans,
as well as convergence and rational continuation. No representation, measure,
or analytic-existence assertion is supplied here.
