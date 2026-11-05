# Compact differentiation on actual automorphic tensors with analytic coefficients

This internal construction uses an actual `OperatorRealization S` and the full
coefficient space `AnalyticSpace e ρ` of a genuine algebraic matrix
representation. Its compact action is the previously constructed diagonal
action on the original algebraic tensor product
`S.Space ⊗[ℂ] AnalyticSpace e ρ`. Its complex Lie action is the previously
constructed diagonal action, using the actual automorphic differential and
the genuine analytic coefficient differential.

`tensorAnalyticCoordinates` composes the original coefficient coordinate
equivalences with Mathlib's finite-product tensor equivalence
`TensorProduct.piScalarRight`. It identifies this tensor product with
`m → S.Space`. On `f ⊗ v`, coordinate `i` is `vᵢ • f`.
`tensorAnalyticEvaluation x i` evaluates that actual automorphic vector at the
adelic point `x`; its value on `f ⊗ v` is `vᵢ * f(x)`.
`tensorAnalyticEvaluation_ext` proves that all these evaluations separate
tensors: finite coefficient coordinates separate the tensor product, and
`S.toContinuous` and actual function evaluation separate each coordinate.

`tensorAnalyticCompactCurve_evaluate_deriv` differentiates the original
diagonal compact action along any compact curve through the identity having
the specified real matrix tangent `X`. On a pure tensor, the scalar product
rule combines the previously proved automorphic compact curve derivative with
the previously proved coefficient compact curve derivative. The two terms are
exactly the evaluation of the diagonal Lie action

```
D(X)(f ⊗ v) = D_S(X)f ⊗ v + f ⊗ D_ρ(X)v.
```

Tensor induction extends this scalar derivative to every tensor. It does not
place a topology on the tensor product or on `S.Space`.

For a tensor-valued alternating cochain `f` equivariant under every element of
the full standard compact subgroup, `tensorAnalyticCochain_compact_real`
chooses an actual compact tangent curve for a real compact Lie vector `Y`.
Apply each `tensorAnalyticEvaluation` to the equivariance equation. The tensor
curve derivative differentiates the output side; the existing compact adjoint
scalar cochain derivative differentiates the input side as the sum of the
positive bracket insertions. Uniqueness of scalar derivatives and separation
by all evaluations give the identity on tuples of complexified real vectors.
The public multilinear scalar-extension theorem then extends it to arbitrary
complex tuples.

Tensor induction in `Y` proves `tensorAnalyticCochain_compact_complex`:
the actual compact Lie action on `f(X)` is
`∑ j, f (Function.update X j ⁅compactComplexInclusion Y, X j⁆)`.
`tensorAnalyticInfinitesimalCompactCochains` is the submodule defined by this
identity. `tensorAnalyticCompactEquivariantLieInclusion` retains every original
full-compact-equivariant cochain, with infinitesimal membership supplied by the
derived theorem. Its underlying alternating map is unchanged and the inclusion
is injective.

All constructions retain an independent number-field universe, arbitrary
finite small coefficient and selected-embedding indices, either selected
orientation of a complex place, the entire coefficient carrier, and every
cochain degree. Empty index types, rank zero and degree zero are included.
No compact infinitesimal compatibility or analytic/algebraic differential
comparison is assumed. Relative coefficient cohomology and identification
with the algebraic coefficient action are subsequent constructions.

The provenance is internal composition of the published tensor, coefficient,
compact-curve and scalar cochain constructions. No new correspondence with an
original literature definition or theorem is claimed.
