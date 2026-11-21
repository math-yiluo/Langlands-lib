# Same-level lifting from the full cuspidal coefficient equality

Waldspurger uses the coefficient equality and translation equivariance of the
central projection in VIII.5 to place the bi-invariant coefficients of a
discrete-series class in the central image at the same level.

`RationalCuspidalDiscreteCoefficientLowerInclusionStatement.of_lifted` applies
the published carrier-lift inclusion of coefficient sums. The lift preserves
the matrix coefficients, square integrability with respect to the given
quotient Haar measure, and the central action. Thus the lower inclusion at
carrier universe `max u uV` implies the lower inclusion at `uV`.

`RationalCuspidalLiftingFromEqualityStatement` is the implication from the
published full equality to the published same-level preimage proposition.
Its proof `rationalCuspidalLiftingFromEquality` applies the carrier lift to
the lower inclusion of the equality. The published central convergence
theorem and compact averaging then give an actual cuspidal Schwartz preimage
at the chosen compact open level. The central character, Haar measures,
Schwartz realization and level are those of the original targets.

The argument uses J.-L. Waldspurger's *La formule de Plancherel pour les
groupes p-adiques (d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003),
VIII.4.2 and VIII.5, printed pp. 330–332, registered as
`waldspurger-2003-plancherel`. The carrier lift implements the universe
conventions of the Library statements.
