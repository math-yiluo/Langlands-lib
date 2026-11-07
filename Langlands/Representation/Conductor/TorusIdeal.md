# The algebraic ideal step for essential vectors

This internal development isolates the weak Nullstellensatz argument in
Jacquet, *A correction to Conducteur des représentations du groupe linéaire*
(2012), §3, printed page 523. It does not construct an essential vector or prove
any of the three clauses of `EssentialConductorStatement`.

`TorusPolynomialAlgebra σ K` is the localization of the polynomial ring at the
product of its variables. Over a field, inverting that product inverts every
variable, so this is the Laurent coordinate ring of the split torus. The
coordinate index type is finite and may be empty. `torusPolynomialEvaluation`
is evaluation at a tuple of units.

The proof first establishes the weak Nullstellensatz for any finite type
algebra over an algebraically closed field. A proper ideal lies in a maximal
ideal. The quotient field is a finite algebraic extension by Zariski's lemma,
and an embedding of that quotient into the base field gives a field-valued
point annihilating the original ideal. This contradicts the stated absence of
a common zero.

Every field-valued point of the Laurent coordinate ring comes from a unit tuple:
the image of the inverted product is a unit, so each coordinate is nonzero;
the universal property of localization identifies the point with evaluation.
This gives `torusIdeal_eq_top_of_no_common_zero`.

`torusSubalgebraIdeal_eq_top_of_no_common_zero` descends the criterion to an
integral subalgebra by extending the ideal to the Laurent ring and using that
an injective integral extension reflects the unit ideal.

`torusPolynomialPermutation` extends polynomial variable renaming to the
localization. Its identity and composition laws give the action of the finite
permutation group. `symmetricTorusSubalgebra` consists exactly of Laurent
polynomials fixed by every coordinate permutation. The full Laurent ring is
integral over this subalgebra: Mathlib's finite-group invariant theorem uses
the monic orbit polynomial `∏ g, (T - g • p)` to prove this. Thus
`symmetricTorusIdeal_eq_top_of_no_common_zero` has no assumed integrality
premise. It states that if, at every unit tuple, some element of an ideal of
symmetric Laurent polynomials evaluates nontrivially, the ideal is the entire
symmetric Laurent ring.

This is the algebraic conclusion used on printed page 523 of Jacquet 2012,
after Lemma 5 on pages 522–523 establishes the ideal property and Lemma 4
supplies pointwise nonvanishing. The implementation treats any algebraically
closed coefficient field; Jacquet uses the complex numbers. The proof of the
algebraic step uses integral descent instead of a presentation by elementary
symmetric functions. The analytic transform, its ideal property, and its
pointwise nonvanishing still require their separate constructions. In
particular this internal helper does not prove or assume the essential-vector
identity, any factor comparison, or any conductor or fixed-vector conclusion.
