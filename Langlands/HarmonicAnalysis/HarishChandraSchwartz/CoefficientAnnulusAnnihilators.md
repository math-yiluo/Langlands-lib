# Invertible annihilators from a fixed-level spectral annulus

This derived module gives the quantitative full-exponent recurrence needed to
recover a coefficient function from a forward tail. The source space is stable
under the specified component and has dimension at most `d`; every occurring
exponent value at the specified point has norm between `η` and `Λ`, where
`0 < η ≤ 1 ≤ Λ`.

The existing fixed-level decomposition expresses any coefficient sum from
this space using at most `d` actual exponent labels, each with nilpotence order
at most `d`, independently of the number of coefficient summands. The product
of the corresponding linear factors to the power `d` annihilates the original
function and has degree at most `d*d`. Its roots retain the stated annulus.
The monic root formula bounds every coefficient by `2^(d*d) Λ^(d*d)` and the
norm of its constant coefficient from below by `η^(d*d)`.
`HasBoundedRightAnnihilator` packages the degree and coefficient bounds, the
lower bound on the constant coefficient norm, and annihilation under right
translation. The product retains its positive lower bound because all its
factors come from the nonzero exponent values.

Applying the modular-inverse tail estimate then bounds each original function
value in norm by an explicit constant times the sum of the individual norms
of the finitely many translated values, starting at any prescribed forward
exponent. Dimension, root annulus and tail starting point determine the
constant.

The contextual original source is Waldspurger, *La formule de Plancherel pour
les groupes p-adiques, d'après Harish-Chandra* (2003), VI.2.1 and VI.2.3,
printed pp.297–300, source `waldspurger-2003-plancherel`. The annulus,
constant-coefficient estimate and backward recovery are derived project
content. Actual orbit annulus realization and tail coefficient bounds remain
to be supplied when applying this intermediate result.
