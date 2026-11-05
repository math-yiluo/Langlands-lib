# Genuine coefficient orbit differentiation and the real analytic Lie action

This internal construction uses the actual smooth orbit realization and the
constructed Frechet derivative of the original archimedean coefficient point
action. It needs no analytic-versus-algebraic differential comparison premise.

At the identity, the genuine finite-coordinate vector function differential
of `smoothOrbitMap v` equals `analyticRealDifferential X v`. The actual orbit
coordinate extension agrees on units, and its proved HasFDerivAt witness
identifies the derivative. No default value of total Frechet differentiation
is used.

The original representation multiplication law identifies left translation
of the orbit function with postcomposition by the original coefficient
endomorphism. That endomorphism is continuous because the coefficient space
is finite-dimensional. The supporting finite vector calculus proves that
real differentiation commutes with both this fixed coefficient map and left
translation. Evaluation at the identity therefore gives, on every group
element, the intertwining equation

```text
smoothOrbitMap(analyticRealDifferential(X)(v))
  = finiteVectorSmoothDifferential(X)(smoothOrbitMap(v)).
```

`analyticRealLieAction` is the same constructed real-linear differential,
now bundled as a real Lie homomorphism into the complex-linear coefficient
endomorphisms. Its bracket law is proved by applying the injective actual
orbit map, using the intertwining equation and the existing genuine vector
function Lie action. Thus neither the bracket law nor an identification
with an algebraic differential is supplied as an input.

The full coefficient space and all selected oriented embedding labels are
retained, including both complex-place orientations. The number-field
universe is independent; selected-label and coefficient indices are small
and finite. Empty indices and rank zero are allowed.

The provenance is internal composition of the existing actual coefficient
orbit and Frechet derivative constructions, scalar/vector smooth calculus,
the representation multiplication law and injectivity of orbit functions.
Agreement with the separately constructed dual-number differential,
complexified algebraic coefficient action, compact infinitesimal insertion,
relative coefficient cohomology, weights and occurrence remain separate.
