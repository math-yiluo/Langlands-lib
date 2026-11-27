# Selecting supported representatives in Arthur's sigma sum

`exists_sigmaCoset_representatives_with_bound` fixes nested standard
parabolics, compact Siegel factors for the given Iwasawa subgroup and
the chamber and truncation parameters. It uses a smooth structure and
a matrix representation of positive size. For a finite plot-smooth
left `G(F)`-invariant function of uniformly moderate growth and each
natural order `m`, one constant bounds the weighted summands at all
norm-one inputs. For each input the choice of rational representatives
is injective on the right cosets. The weights are the \(m\)-th powers
of the normalized adelic heights of the chosen translates.

In Arthur's regrouped truncation formula (13.7), the coefficient is the
product of the lower truncated Siegel indicator and the relative sigma
function. Each factor takes values zero and one. If the product is one,
the Siegel indicator supplies a rational point of the lower parabolic
sending the original coset representative into the truncated Siegel set.
Multiplication by that point on the left keeps the right coset fixed.
The sigma function is invariant under this change by its expansion in
relative and hatted chamber functions. Each constant term of the signed
interval is invariant under that rational point as well.

Rational translation preserves the ambient norm-one subgroup. In the
Siegel factorization of the translate, the unipotent and norm-one Levi
factors and the point of the compact subgroup are also ambient norm
one. This puts the positive torus coordinate in the same norm-one
subgroup. The Iwasawa height of the translate is the height of that
torus coordinate, so the alternating term decay estimate applies on
the resulting truncated sigma region. The coefficient-zero terms
satisfy the bound with any representative. Different right cosets give
distinct chosen rational points, so the weighted bounds can be added
using rational height summability. This carries out the reduction to
summand bounds in Arthur 2005, §13, pp. 71–72.
