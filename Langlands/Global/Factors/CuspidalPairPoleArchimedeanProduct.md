# The initial archimedean product for cuspidal pairs

`archimedeanPairProduct` is the product over the real and complex places of
the reciprocal denominators of the pair factors used in
`CuspidalPairPoleStatement`. The actual block lists are inputs.

The right-half-plane nonvanishing theorems for the denominators come from
`AssociatedGammaCuspidalEquation`. A finite family shares a cutoff by
taking the sum of the absolute values of its individual cutoffs. On the
resulting half-plane the reciprocals are analytic since the denominators
are entire. Taking the two finite products and intersecting their half-planes
proves analyticity of the archimedean product. Multiplying by a finite Euler
product continuous on a right half-plane gives continuity of the initial
completed product, the hypothesis used in the continuation from normalized
tests.

The multiplication of the finite and archimedean local factors is the global
product in J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004), §4,
printed pp. 218–219 (PDF pp. 221–222). The registered source
`cogdell-2004-analytic-theory-gln` has SHA-256
`8117f145869274324b12344dc83fa3289e3bd27c515b8d0d4a0211cd64174944`.
The analytic lemmas here derive a common half-plane from the Library's
right-half-plane regularity results for these Gamma factors.
