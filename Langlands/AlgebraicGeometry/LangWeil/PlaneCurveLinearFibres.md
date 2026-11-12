# Linear fibres of an absolutely irreducible plane curve

Author: Worker 2969.

This module develops the elementary linear-fibre argument associated with
printed p.349 of Wolfgang M. Schmidt, *Zur Methode von Stepanov*, Acta
Arithmetica 24 (1973), registered source
`schmidt-1973-zur-methode-von-stepanov`. The implemented target allows the
zero-count error to be at most the first partial degree. For example,
`XY - 1` has one fewer rational zero than the size of the field, so the
source's printed exact-count assertion for every linear-in-one-variable
case cannot be used without qualification.

The proof writes the actual polynomial as `a(X)Y + b(X)`. Its coefficient
`a` is nonzero, and its univariate degree is at most the first partial
degree of the original polynomial. To prove there is no common field
root of `a` and `b`, transport to a polynomial in `Y` with coefficients
in the one-variable polynomial ring. A common root would give the
nonunit factor `X - x` in both coefficients. Irreducibility forces the
other factor to be a unit, contradicting degree one in `Y`.

The module also proves the needed reflection of absolute irreducibility
to irreducibility over the original field: a polynomial whose scalar
extension is a unit must itself be a nonzero constant.

For the actual fibre-count equivalence, project each rational zero to its
first coordinate. At a nonexceptional abscissa the unique second
coordinate is `-b(x)/a(x)`; the no-common-root result excludes every point
over an exceptional abscissa. Thus the number of rational zeros plus the
number of field roots of `a` equals the field size. The usual univariate
root bound bounds the absolute error by `a.natDegree`, hence by the first
partial degree. This proves the second clause of the elementary reductions
interface.

The helper `planeCurve_iterated_specialization_ne_zero` generalizes the
same factor argument to every positive outer degree. If specialization at
an abscissa were the zero polynomial, `X - x` would divide every coefficient
and hence the whole polynomial; irreducibility would then force outer
degree zero. Applying the univariate root bound after specialization gives
`planeCurve_fibre_count_le`: every actual rational fibre has at most the
second partial degree. This general fibre bound supplies an elementary
input to the later norm-polynomial construction.
