# Bi-smooth coefficients of actual subquotients

This module states two elementary coefficient inclusions. It supplies no proof.
Both declarations are closed proposition definitions and use the unchanged
`GodementJacquet.biSmoothMatrixCoefficients` from `GodementJacquet.Zeta`.

`Langlands.GodementJacquet.SubquotientCoefficientInclusionStatement` quantifies
over a topological group `G` for which compact open subgroups are cofinal among
open subgroups. It quantifies over independent complex module carriers `V`
and `W`, representations `σ` and `τ` on those carriers, and smoothness of `σ`.
For every actual subrepresentation `A` of `σ` and every surjective intertwiner
`q : A.toRepresentation.IntertwiningMap τ`, its conclusion is

```text
biSmoothMatrixCoefficients τ ≤ biSmoothMatrixCoefficients σ.
```

The group and the two carrier universes remain independent. The witness is an
actual subrepresentation followed by an actual surjective intertwiner. No
categorical carrier choice, irreducibility, admissibility, finite length,
finite generation, or chosen model equivalence is assumed. Smoothness of the
target is not an additional premise.

`Langlands.GodementJacquet.Padic.SubquotientCoefficientInclusionStatement`
states the specialization for every canonical p-adic field and every
`GL_(n+1)`, including `n = 0`. It uses exactly the canonical field topology,
retains independent field and carrier universes, and has no compact-open
cofinality premise. The remaining premises and the conclusion are identical.
There is no Haar measure or additive character in either assertion, because
the coefficient submodules do not depend on them.

## Internal provenance and proof obligation

This is an internal algebraic prerequisite for restricting a matrix functional
equation to the actual constituent used in JPSS (1983), Section 5.4, printed
page 423. It is not a transcription of a separately numbered source theorem.
It is formulated using the published smooth-dual exactness API.

The motivating source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin–Selberg Convolutions* (1983), Section 5.4, printed page 423
(one-based PDF page 58), equation (5) and the coefficient restriction directly
below it. The registered source is `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`,
retained at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
That passage motivates the constituent application; it does not separately
state the general topological-group assertion formalized here. This module
asserts none of the passage's analytic or gamma-factor conclusions.

For a generator coefficient of `τ`, the intended proof first pulls its smooth
functional back along `q`. The inherited representation of `A` is smooth by
injectivity of its inclusion into the smooth representation `σ`. The published
`Langlands.contragredientMap_surjective_of_injective_of_compact_cofinal`
from `Smooth.Contragredient.ExactProof` can then extend that smooth functional
from `A` to `σ`. A vector lifts through the actual surjection `q`, and
smoothness of `σ` ensures its lift and its image in `σ` are smooth.
Equivariance should identify the resulting coefficient functions pointwise.
Passing to their complex spans should give the conclusion. This paragraph is
a proposed proof route; this statement module does not implement it.
The p-adic proof must additionally discharge compact-open cofinality for the
canonical general-linear group.

The inclusion would allow assertions quantified over all ambient coefficient
functions to be restricted to the constituent family. In particular the same
convergence bound, rational continuation formula, and functional-equation
formula could be retained after constructing the relevant subtype witnesses.
It does not assert that an ambient normalized generator generates the smaller
constituent value module. No analytic existence, generator identity, Fourier
identity, representation equivalence, gamma-factor equality or L-factor
divisibility is stated here.

## Authorship

Worker 468 authored the prepared Lean and Markdown draft. Worker 55 checked
the actual coefficient definitions, the smooth-dual extension API and the
canonical topology, retained the Lean draft unchanged, and prepared this
statement pair for review and publication.
