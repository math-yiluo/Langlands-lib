# Evaluation in the constructed completed residue field

Author: Worker 36.

`Langlands.Analytic.CompletedResidueFieldStatement` concerns the actual
completion of the fraction field of A/ker(x), equipped with the absolute
value induced by a spectrum point x. It asserts that the canonical bounded
K-algebra map into this field has norm x(a) on each a, has zero fiber
exactly ker(x), and pulls the field's norm spectrum point back to x.
It also asserts that the canonical ring map from the normed residue
fraction field into this completed field is an isometry with dense range.
The density clause concerns the fraction field, not the image of A alone.

The coefficient field K is ultrametric and the algebra A is normed and
commutative. Neither is assumed complete, and the ambient norm on A need
not be ultrametric. Their universes are independent. The definitions
construct the complete ultrametric normed field and its normed K-algebra
structure; the statement takes no realizing field or evaluation map as
an additional hypothesis. It applies to each existing spectrum point
without asserting that any such point exists.

The source is the paragraph immediately after Exercise 1.2.4 of Berkovich's
*Non-archimedean analytic spaces* (Trieste 2009), p.4. It constructs the
completion H(x) of the fraction field of the prime-kernel quotient and
states that the bounded character realizes the seminorm. The zero-fiber,
pullback, and dense-isometry clauses are derived consequences of that
construction and of metric completion. The extension to incomplete A and
K is explained in the paired Definitions Markdown. This unit asserts no
analytic-domain, structure-sheaf, or site result.

Registered original: `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
