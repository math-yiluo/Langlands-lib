# Actual orbit equivariance and analytic coefficient covariance

This internal construction packages the original full coefficient orbit map
as `analyticOrbitIntertwiner`. Its domain is the entire `AnalyticSpace` with
the original scheme-point representation; its codomain is the actual smooth
finite-vector function space with right translation. The representation
multiplication law proves equivariance. Evaluation at the identity, through
the existing orbit injectivity theorem, proves that this intertwiner is
injective. The previously constructed genuine orbit differentiation theorem
also identifies its values on every analytic Lie action.

Apply that injective orbit embedding to both sides of the coefficient
covariance equation. Equivariance and analytic Lie intertwining reduce it
to the proved full-group covariance of actual vector differentiation.
This proves `analyticRepresentation_lie` for every group element, every
complexified Lie vector and every original coefficient vector. The Lie
action is the one constructed from the real Frechet differential; no
equality with the algebraic dual-number differential is used.

`analyticCompactRepresentation` restricts that original point action to the
entire standard compact subgroup. Its Lie covariance is a specialization
of the full-group result. The existing diagonal tensor theorem then proves
full-compact covariance on every tensor of an actual `OperatorRealization`
with `AnalyticSpace`. Its coefficient covariance premise is discharged by
the constructed theorem, rather than supplied as additional input.

The field universe remains independent, and all finite selected embedding
labels, either complex-place orientation and all original coefficient
vectors are retained. Empty labels and rank zero are permitted. No topology
on the smooth function space is assigned. Equality with the separate
algebraic coefficient Lie action, compact infinitesimal insertion and
coefficient relative cohomology remain separate obligations.
