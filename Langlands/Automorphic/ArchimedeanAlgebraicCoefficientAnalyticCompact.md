# Actual compact differentiation and insertion for analytic coefficients

This internal construction differentiates the original compact group action
on the entire `AnalyticSpace`. `analyticCompactCurve_deriv` composes the proved
Fréchet derivative of the genuine coefficient orbit extension with any actual
compact curve through the identity having the specified real matrix tangent.
The extension agrees with the original point representation on every group
element. Its derivative is the previously constructed analytic Lie action.
No analytic versus algebraic differential comparison is used.

For a coefficient alternating cochain equivariant under the full standard
compact subgroup, choose the actual compact tangent curve for a real compact
Lie vector. Apply each coefficient coordinate to its equivariance equation.
The actual coefficient curve derivative differentiates the output side.
The existing scalar compact adjoint cochain derivative differentiates the
input side as the sum of bracket insertions. Uniqueness of derivatives and
all coefficient coordinates prove `analyticCochain_compact_real`.

Complex multilinearity extends the input tuple to arbitrary complex Lie
vectors. Tensor induction in the compact Lie direction then proves
`analyticCochain_compact_complex` for every vector in the full complexified
compact Lie algebra. This is an actual derived infinitesimal insertion
identity in every degree, including degree zero.

`analyticInfinitesimalCompactCochains` is the submodule cut out by that
identity. `analyticCompactEquivariantLieInclusion` retains each original
cochain and proves its infinitesimal membership using the differentiation
theorem. Its underlying alternating map is unchanged, and it is injective.
No infinitesimal compatibility certificate is supplied.

The number-field universe is independent; all finite selected embedding
labels, either complex-place orientation, the full original coefficient
carrier, empty indices and rank zero are retained. No topology on automorphic
or smooth function spaces is introduced. Automorphic tensor insertion and
relative coefficient cohomology are subsequent constructions; algebraic
differential comparison, weights and automorphic occurrence remain separate
obligations.
