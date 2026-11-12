# Positivity of binary products with unitary top shifted derivatives

Author: Worker 105.

`Langlands.Classification.BernsteinUnitaryTopDerivativeProductPositivity F T`
states the product-positivity implication used in the rank induction for
Bernstein's unitary-product theorem. It is a proposition definition. No
product-positivity theorem is proved in this file.

The source is J. N. Bernstein, *P-invariant distributions on GL(N) and the
classification of unitary representations of GL(N)*, LNM 1041 (1984),
registered as `bernstein-1984-p-invariant`. Section 8.2, printed page 88
(PDF page 39), derives preservation of G-positivity from the shifted-derivative
Leibniz formula. The ingredients are the shifted derivatives of section 7.2
(PDF page 33), the ring-homomorphism identity for shifted derivatives in
section 7.5 (PDF page 35), the addition of scalar central exponents under
products in section 7.8 (PDF page 37), and exponent zero for unitary
representations in section 7.3 (PDF page 33).

The statement is a sufficient specialization of that product argument.
It quantifies over two actual finite-length smooth representations `A` and
`B`, feasible derivative bounds `r` and `s`, vanishing of all derivatives
above those bounds, strict positivity of all shifted derivatives below
each bound, and unitarizability of both shifted derivatives at the bounds.
It concludes strict positivity of the actual shifted derivatives of the
actual binary normalized product at all feasible orders below `r + s`.

The top derivatives are assumed unitarizable, so every central exponent
of either is zero. In the shifted Leibniz filtration at order `k < r + s`,
a surviving term has derivative orders `i ≤ r` and `j ≤ s` with `i + j = k`.
At least one inequality is strict. Its shifted derivative has positive
central exponents, while the other factor has positive or zero central
exponents. Addition of scalar central exponents therefore gives positivity
of each surviving term and hence of the filtered object. This explains
the provenance of the proposed implication; the necessary actual-object
filtration, twisting, finite-length and exponent arguments remain proof
obligations.

No existence or nonvanishing at the supplied bounds is required. In
particular `r` and `s` may be zero, and either ambient rank may be zero.
These are useful derived boundary cases of the same filtration argument:
the empty lower-order range is vacuous, the zero object has no
irreducible subquotient exponents, and the same scalar-character formula
is used on `GL_0`. The statement makes no unrestricted equivalence between
two arbitrary exponent-set comparisons.

The finite-length assumptions concern the actual factors. Derivative
finite length, exponent existence where needed, and passage through the
Leibniz filtration are to be proved from them. All topologies and the
unitary additive character are supplied, and the field and representation
carrier universes are independent.
