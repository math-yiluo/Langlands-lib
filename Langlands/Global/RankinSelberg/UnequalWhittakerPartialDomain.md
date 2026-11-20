# Removing the away coordinates of ordinary unequal-rank Whittaker tests

`UnequalPairDependsOnRetained` states that the padded ordinary product
agrees on the partial domain with the product at the retained coordinates.
On that domain, a matrix of the smaller rank decomposes into
a left unipotent, its retained coordinates, and a right factor
integral away from `S` and trivial at the retained places. Padding
carries the unipotent to the larger group and preserves its generic
character. The two unipotent multipliers cancel because the second
Whittaker function uses the inverse character.

The smaller pure tensor vector is fixed by the away factor. Padding
that factor gives a finite adelic matrix that remains integral away
from `S` and trivial on `S`. The larger pure tensor vector is fixed by
this action as well. The resulting paired product is evaluated at the
retained coordinates and their padded image. This is the unequal-rank
variant of the Library's ordinary partial-domain reduction.

The calculation supports the factorization of the ordinary partial
integral in J. W. Cogdell, *Analytic theory of L-functions for GL_n*
(2004), §4.1, printed pp. 219–220 (PDF pp. 222–223). The implemented
proof uses the Library's decomposition of partial quotient classes,
Whittaker covariance, and finite pure tensor invariance.
