# Positive upper-Jacquet counts for subrepresentations of induction

This internal proposition concerns the existing actual normalized upper
induction `induced T B σ` and upper normalized Jacquet object `upperJacquet`.
It quantifies over every prime, p-adic field, supplied compatible topology,
rank and block shape. The field, inducing carrier and subrepresentation
carrier universes are independent.

Suppose the product-Levi representation σ is irreducible and an algebraic
GL representation P admits an injective nonzero intertwiner into this
induction. If the upper Jacquet module of the induction has an actual finite
simple series counting σ exactly M times, the upper Jacquet module of P has
such a series counting σ exactly m times, with `0 < m` and `m ≤ M`.
The injection and its nonzeroness are both explicit hypotheses. No
irreducibility or separate smoothness hypothesis on P is present.

The provenance is internal: this is the concrete upper-Jacquet specialization
of existing smooth coinvariant injectivity, nonzero evaluation into normalized
parabolic induction, and actual-series simple-map detection. An injective
intertwiner into the smooth induction also makes P smooth. Evaluation gives
a nonzero map from its upper Jacquet module to σ; this alone supplies no
finite series. The ambient multiplicity hypothesis supplies the finite
series needed for a positive bounded count.

This file defines the proposition only. It does not prove the proposition,
an ambient multiplicity value, second adjointness, a quotient detector,
unconditional Jacquet finite length, or a segment constituent. Its sole
project import is `CuspidalJacquetMultiplicityStatement`, which supplies
the actual induction, quotient objects and multiplicity predicate. No
classification conclusion is asserted or used.
