# Analytic polynomial solution charts over complete fields

The variables split as `τ ⊕ σ` with both index types finite. For equations
`p : σ → MvPolynomial (τ ⊕ σ) k`, `polynomialCoordinateMap` consists of the
free variables and all relation values. Its derivative is the free projections
paired with formal polynomial derivatives. An invertible dependent Jacobian
forces injectivity of this derivative, and equality of the finite dimensions
gives bijectivity. The resulting linear equivalence is continuous over the
complete coefficient field.

The ambient map is analytic because polynomial evaluation is `ContDiff` of
every order. `AnalyticAt.hasStrictFDerivAt` gives its strict derivative;
`HasFDerivAt.fderiv` identifies it with the displayed derivative. The strict
inverse function theorem gives an ambient open partial homeomorphism at each
solution. This is the essential change from the real or complex construction:
no inference from ordinary differentiability to strict differentiability is
used over a general normed field.

`polynomialFibreChart` restricts that map to the zero fibre using the published
`zeroFibreChart`. Its forward map is exactly the free-coordinate projection and
its source contains the chosen solution. The published zero-fibre inverse
lemma, used at order `ω` with the same nonsingular derivative at all solutions,
gives analytic inverse inclusion. Polynomial evaluation along that inclusion
is then analytic by composition.

This is an internal adaptation by Worker 115 of Worker 362's published
`PointManifold.PolynomialFibreCharts`, retaining its polynomial derivative and
zero-fibre helpers by import. It includes empty variable or relation index sets.

Throughout this module, `k : Type u` is an arbitrary complete nontrivially
normed field, the scheme is affine over `Spec k`, and its actual point carrier
is `PointTopology.RingPoint k X k` with its published evaluation topology.
The analytic order is `ω` over `k`. There is no characteristic, archimedean,
positive-dimension or point-nonemptiness assumption.
