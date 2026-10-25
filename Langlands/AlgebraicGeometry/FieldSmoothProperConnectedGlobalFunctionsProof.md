# Proof of the field global-functions proposition

Authors: Worker 129 and Worker 428. Worker 129 constructed the helper
proof and this wrapper; Worker 428 checked the implementation and prepared
the exact-target submission.

The theorem
`Langlands.AlgebraicGeometry.fieldSmoothProperConnectedGlobalFunctions.{u}`
has exact type
`Langlands.AlgebraicGeometry.FieldSmoothProperConnectedGlobalFunctions.{u}`.
It imports that proposition by Lean module name, introduces its field,
scheme, morphism, and three geometric hypotheses, then applies
`Langlands.AlgebraicGeometry.GlobalFunctionsFieldProof.isIso_appTop_of_field`.
The implemented argument and source correspondence are documented in
[GlobalFunctionsFieldProof.md](GlobalFunctionsFieldProof.md).

The theorem covers every field `K : Type u` and every scheme
`X : AlgebraicGeometry.Scheme.{u}`, in arbitrary universe `u`.
For `p : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of K)`, the hypotheses
are exactly `AlgebraicGeometry.Smooth p`,
`AlgebraicGeometry.IsProper p`, and
`AlgebraicGeometry.GeometricallyConnected p`.
The conclusion is `CategoryTheory.IsIso p.appTop`, invertibility of
the specified canonical map on global sections.
The imported proof uses reducedness, integrality, and connectedness over
the algebraic closure, followed by flat base change of sections and
faithfully flat descent. It adds no hypotheses to the published target.

The source is Stacks Project Varieties Lemma 33.9.3(7), Tag
[0BUG](https://stacks.math.columbia.edu/tag/0BUG), together with
Lemma 33.25.4, Tag [056T](https://stacks.math.columbia.edu/tag/056T).
Their exact retained source and the different implemented proof route
are described in the companion helper Markdown.
