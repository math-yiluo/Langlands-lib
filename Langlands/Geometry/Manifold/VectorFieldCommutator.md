# Scalar differential commutators on manifolds

`Langlands.Geometry.Manifold.smoothVectorFieldCommutator_proof` proves the
existing proposition
`Langlands.Geometry.Manifold.smoothVectorFieldCommutator I M`, imported from
`Langlands.Geometry.Manifold.VectorFieldCommutatorStatement`.
Its model is an arbitrary complete real normed space, its specified model with
corners is boundaryless, and its manifold is smooth. The tangent-bundle sections
of the two vector fields are assumed differentiable. For every smooth
complex-valued function, the conclusion is

```
df_x([V,W]_x)
  = d(y ↦ df_y(W_y))_x(V_x) - d(y ↦ df_y(V_y))_x(W_x).
```

Here every scalar derivative is the actual `mvfderiv`, and the bracket is the
actual `VectorField.mlieBracket`. All differentiation uses the real scalar
field; the complex codomain is a real normed space. The model, chart model and
manifold have independent universes, and no finite-dimensional or group
hypotheses are introduced.

The proof is an internal calculus consequence of the imported Mathlib
definitions and `VectorField.fderiv_apply_lieBracket` in
`Mathlib/Analysis/Calculus/VectorField.lean`. It does not claim an independent
literature proof or an adelic application. The implemented route is as follows.

The private lemma `scalarDerivative_in_chart` identifies `mvfderiv I g x` with
the ordinary real Fréchet derivative of `g ∘ (extChartAt I x).symm` at the chart
point. It applies to an arbitrary scalar function. In the differentiable case,
it uses `MDifferentiableAt.mvfderiv` and the identity target chart. In the other
case, differentiability of the coordinate expression would imply manifold
differentiability by
`DifferentiableWithinAt.mdifferentiableWithinAt_of_comp_extChartAt_symm`;
both derivative constructions therefore take their defined zero value.
Boundarylessness supplies `range I = univ`.

The private lemma `directionalDerivative_in_chart` treats a differentiable
scalar function and an arbitrary tangent vector field. On the open target of
the chart, the chain rule `mvfderiv_comp` expresses the derivative of the scalar
coordinate function as its manifold derivative composed with the derivative
of the inverse chart. The chart field is precisely
`VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Y (range I)`.
The inverse-chart derivative is invertible, so its composition with the
inverse used in this pullback cancels. Thus the scalar directional derivative
in coordinates agrees with the derivative of the scalar coordinate function
applied to the chart field throughout a neighborhood of the chart point.

For the main theorem, write `φ = extChartAt I x`, `z = φ x`, and let `V'` and
`W'` be these actual pullbacks of `V` and `W`. Smoothness of `f` and the inverse
chart gives `ContDiffAt ℝ ∞ (f ∘ φ.symm) z`. The hypotheses on the tangent-bundle
sections give differentiability of `V'` and `W'` at `z` by
`MDifferentiableWithinAt.differentiableWithinAt_mpullbackWithin_vectorField`
from `Mathlib/Geometry/Manifold/VectorField/LieBracket.lean`. This imported
pullback regularity result uses completeness of the model.

At the chart basepoint, `mfderiv_extChartAt_self` is the identity, and
`mfderivWithin_extChartAt_symm_inverse_apply` identifies the pullback-field
values with the original tangent vectors. Unfolding the definition of
`mlieBracket` therefore gives `lieBracket ℝ V' W' z`. Apply
`VectorField.fderiv_apply_lieBracket` to `f ∘ φ.symm`, `V'` and `W'`. Finally,
the two private chart lemmas and
`Filter.EventuallyEq.fderiv_eq` transport its iterated derivatives back to the
manifold. The sign is differentiation first along `W`, then along `V`, minus
the reverse order.

The published statement pair and all of its imported files are unchanged.
This proof establishes only the generic scalar commutator; tangent actions on
adelic groups and their representation-theoretic consequences are outside its
scope.
