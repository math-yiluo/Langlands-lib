# Analytic and algebraic differential comparison for actual matrix representations

`AnalyticProductDifferentialComparison rho` is the unproved proposition that
the following two already constructed maps have the same value on every
matrix family X:

- `rho.analyticProductDifferential X`, the real Frechet derivative at the
  identity of the actual evaluated scheme representation in the actual open
  units chart;
- `rho.productDifferential B X`, the B-linear differential recovered by
  evaluating the same genuine scheme representation on the actual
  dual-number identity-kernel point `I + epsilon X`.

The statement compares these exact existing objects, with no alternative
representation, supplied derivative, smoothness witness or covariance
hypothesis. The analytic construction has a proved derivative-existence
witness and independence from ambient values outside invertible families.
The algebraic construction has a proved actual first-order point equation.
Their agreement is an additional compatibility result, not a consequence
asserted by either construction.

The base commutative ring, finite factor index and test algebra share universe
u. Each matrix index is small and finite. The test algebra B is a complete
normed commutative real algebra with its specified base-ring algebra
structure; no topology or norm on the base ring or continuity of its map to B
is assumed. Matrix families are finite, with the specified operator norms
and product topology. Empty factors and rank zero are allowed. The equation
is pointwise in X, so its right-hand side needs no separately supplied
continuity structure.

The provenance is an internal compatibility target: actual regular functions
of a scheme morphism admit the same first-order expansion in real calculus
and dual-number evaluation. A possible proof constructs the first-order jet
of actual regular-function evaluations and uses its additivity and Leibniz
law, or works with finite polynomial/inverse-coordinate presentations.
No proof of that compatibility or generic jet construction is supplied here.
This proposition is intended as an exact independent proof target before
identifying the archimedean analytic coefficient differential with the
existing algebraic Lie action. It asserts no automorphic occurrence or
cohomological comparison.
