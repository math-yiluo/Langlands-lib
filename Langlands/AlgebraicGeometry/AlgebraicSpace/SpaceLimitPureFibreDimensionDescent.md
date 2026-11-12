# Pure fibre dimension of algebraic spaces along cofiltered affine limits

Authors: Worker 156 and Worker 131. The generic common-chart comparison is
Worker 131's published `EtaleMorphismChart.property_of_chart`; the present
specialization and limit argument are by Worker 156.

This unit proves pure fibre dimension alone under the unchanged
finite-presentation-atlas hypotheses of `SpaceLimitPropertyDescends`.
It does not claim nonemptiness or geometric connectedness of fibres.
The existing componentwise pure-dimension definition allows empty fibres.

The four scheme-property callbacks in `SchemeEtalePureFibreDimension` apply
the common-chart comparison to local finite type together with pure fibre
dimension. Consequently the unchanged existential `HasPureFibreDimension`
condition holds on every commuting étale chart square; a surjective source
chart gives an equivalence. Scheme base-change stability also proves that
the space condition is preserved under arbitrary scheme base change.

Choose the fixed affine finite-presentation chart square at the original
stage. Restricting the chart square to a scheme base change preserves
étaleness, surjectivity, and commutativity. Pullback symmetry identifies its
actual scheme map with the base-changed map in the scheme limit theorem.
Both chart schemes are affine and locally of finite presentation over the
original affine base, so the relative scheme morphism has the required
finite-presentation, quasi-compactness, and quasi-separatedness hypotheses.
Its target structure map is quasi-compact and quasi-separated.

Restrict the original diagram along `Over.forget i`. This functor is initial,
so its whiskered cone is still limiting. Its objects retain the actual
incoming arrows to the original stage. The relative scheme pure-dimension
descent equivalence therefore produces precisely the incoming stage witness
in `SpaceLimitPropertyDescends`. Local finite type of every base-changed
chart map supplies the remaining factor of the scheme property.

This is an internal derivation from the imported scheme descent and
chart-comparison results. `SpaceLimitPureFibreDimensionDescentStatement`
quantifies every natural dimension, every small cofiltered affine diagram,
and the original finitely presented quasi-separated spaces in universe `u`.
The geometric-connected-fibre conjunction of the full target remains a
separate obligation.
