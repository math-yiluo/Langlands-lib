# The genuinely differentiated complex analytic coefficient module

This internal construction complexifies the actual real Frechet coefficient
action. `analyticComplexDifferential` is its complex-linear scalar extension,
with pure-tensor value z times the original real differential on X.
Tensor induction and the previously proved genuine real orbit differentiation
show that the actual smooth orbit map intertwines this entire complexified
action with the existing vector function Lie action.

The injectivity of that original orbit map transports the proved vector
function bracket law, giving `analyticComplexLieAction` as a complex Lie
homomorphism. No derivative, Lie law or analytic-versus-algebraic differential
comparison is supplied as an input. Its restriction to pure tensors is
exactly z times the constructed genuine real analytic Lie action.

`AnalyticSpace` retains the entire original coefficient carrier with its
inherited additive, complex-module, finite/free and normed complete structures.
Its complex Lie-module structure is the constructed analytic action.
`analyticCoordinates` is the identity complex-linear equivalence to the
original algebraic coefficient carrier and asserts no compatibility between
their Lie actions. This distinct synonym keeps the original algebraic
Lie-module instance separate until the comparison is proved.
`analyticRepresentation` retains the original full point representation;
the coordinate formulas identify both its point action and the analytic
Lie action with the constructions above.

`analyticReducedLieAction` and `analyticCompactLieAction` are literal
restrictions through the actual reduced and compact complex Lie inclusions.
Their restriction routes agree by the existing inclusion identity. These
restrictions do not assert the separate full-compact infinitesimal insertion
condition needed for relative cohomology.

The field universe remains independent and all finite selected embedding
labels and coefficient vectors are retained, including either complex-place
orientation. Empty indices and rank zero are permitted. Equality with the
existing algebraic dual-number Lie action, full-compact covariance and
infinitesimal insertion, relative coefficient cohomology, weights and
occurrence remain separate obligations.
