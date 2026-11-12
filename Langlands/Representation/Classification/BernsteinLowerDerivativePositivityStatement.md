# Lower shifted-derivative positivity for irreducible unitary representations

Author: Worker 105.

`Langlands.Classification.BernsteinUnitaryLowerDerivativePositivity F T` states
the lower-derivative positivity needed for Bernstein's unitary-product proof.
It is a proposition definition; this file proves no positivity assertion.

The source is J. N. Bernstein, *P-invariant distributions on GL(N) and the
classification of unitary representations of GL(N)*, LNM 1041 (1984),
registered as `bernstein-1984-p-invariant`. Section 7.4, printed page 83
(PDF page 34), gives strict positivity of the central exponents of the shifted
derivatives below the highest positive order for an irreducible unitarizable
representation. Its analytic input is the homogeneous mirabolic-module
unitarity criterion of section 7.3, proved in section 9. Sections 7.2 and 7.3,
printed page 82 (PDF page 33), define the shifted derivatives and central
exponents.

The statement quantifies over every positive rank, the supplied field topology,
every unitary additive character, every actual irreducible unitarizable smooth
representation, and every actual highest positive derivative order. It requires
all actual shifted derivatives of orders strictly below that order to have
strictly positive central exponents, in the sense of
`BernsteinShiftedDerivativePositiveBelow`.

The order-zero condition is included, as in section 8.2, printed page 88
(PDF page 39). This is a derived extension of the positive-order condition in
section 7.4: the order-zero shifted derivative is `ν^(1/2) π`, and a unitary
irreducible `π` has central exponent zero. On scalar matrices in positive rank
`N`, the determinant twist adds `N / 2`, which is strictly positive.
Consequently the statement combines the analytic positive-order implication
with this elementary order-zero boundary. It does not assert the converse
unitarity criterion, a comparison between arbitrary exponent sets, or
irreducibility or unitarity of the highest derivative.

The highest-order datum records nonvanishing at its order and vanishing at all
higher feasible orders; no highest-order existence hypothesis is hidden in
the positivity predicate. Rank zero is outside this assertion and is handled
separately when reducing products to positive rank. The field and carrier
universe parameters are independent.
