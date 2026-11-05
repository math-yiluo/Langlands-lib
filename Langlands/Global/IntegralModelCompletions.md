# Arithmetic integral models on actual finite completions

This derived internal construction specializes a supplied integral model over
the S-integers of a number field to the canonical completed integer ring at each
finite place outside S. All fields and schemes have the same arbitrary universe
parameter. The namespace is
`Langlands.Global.IntegralModelCompletions`.

For a finite set S and a place v outside S, `integerMap` is the existing
S-integer algebra action on the corresponding `NumberFieldLevelFactor`. Its
value, coerced to `FiniteCompletion F v`, is exactly the image of the underlying
element of F under the canonical completion map; `integerMap_coe` proves this
formula. The local algebra and scalar-tower instances implement this commuting
square, using the same canonical maps throughout.

For an actual `IntegralModel` M of G over the S-integers, `model` is its pullback
to `v.adicCompletionIntegers F`, with generic field `FiniteCompletion F v`.
Its generic group is the actual base change of G. The theorem `model_group`
identifies the underlying group scheme with the pullback along `integerMap`.
The theorem `isSmooth_model` preserves a supplied smoothness hypothesis.
The theorem `model_integralPointMap` identifies restriction of each original
integral section followed by generic evaluation with restriction of its original
generic point to the completion.

The subgroup `subgroup` is the image of all sections of this local model in
G's original coefficient-point group
`G.affinePoints (CommAlgCat.of F (FiniteCompletion F v))`, transported by the
specified generic-fibre isomorphism and the canonical base-change comparison.
If the underlying scheme of G is affine, `isCompact_subgroup` proves that this
image is compact for the existing regular-function evaluation topology.

The proofs reuse `IntegralModel.baseChange`, its smoothness and section
compatibility theorems, and
`IntegralModel.isCompact_coefficientIntegralPoints`. The latter applies because
the actual completed integer ring is a compact Hausdorff topological ring and
its inclusion into the completion is continuous. Compactness of that ring is
provided by `IntegralFiniteAdeles`. These are internal consequences of the
published interfaces; no new external source result is asserted here.

The construction requires M as input. It supplies no existence theorem for a
good reductive or parabolic model, no maximality theorem, no parabolic covering
theorem, and no assertion that this image agrees almost everywhere with a
separately chosen integral family. Those remain obligations of consumers.
