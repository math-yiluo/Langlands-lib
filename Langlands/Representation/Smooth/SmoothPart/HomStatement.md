# Smooth-part linear factorization laws: proposition target

Worker 0's `Langlands.SmoothHomLawsStatement` is a proposition definition
containing four explicit clauses for the linear equivalence in
[HomDefinitions](HomDefinitions.md):

1. The forward map has underlying value `f v` in the original target.
2. Its inverse has value given by inclusion of a smooth vector.
3. Postcomposition by an intertwiner `g` corresponds to postcomposition by
   `smoothMap g` after lifting.
4. Precomposition by an intertwiner between smooth sources commutes with
   lifting.

The four reusable clause definitions are, respectively,
`SmoothHomEvaluationStatement`, `SmoothHomInverseEvaluationStatement`,
`SmoothHomPostcompositionStatement`, and `SmoothHomPrecompositionStatement`.
The selected target quantifies `IsTopologicalGroup G` inside its proposition.
The coefficient ring is commutative and the three carriers have independent
universes. Source smoothness is explicit in each clause; the precomposition
clause requires both source representations to be smooth. No target smoothness
is assumed. Inverse and linearity laws already belong to the constructed
linear equivalence, so these clauses do not duplicate its structure fields.

These formulas are internal consequences of the explicit maps. Their source
context and exact accepted smooth-part dependency are documented in
[HomDefinitions](HomDefinitions.md), with Casselman Chapter II, Section 1,
page 2, first two paragraphs, literature ID
`casselman-2019-smooth-representations`, SHA
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
They are not presented as quotations of a numbered source theorem.

This pair defines the target without assuming or proving its clauses. Its
sole direct construction import is `HomDefinitions`, accepted artifact
`e17aa7ac-f4d5-4ac3-84f2-b7c706899ce0`, version 1, published at commit
`e733f3dda0099f9951b5c427fc3783c2ebdf3f45`, independent receipt
`9036a150-9d97-4d10-91a7-c0efa7f5f008`. A completed fetch verifies that
publication is current, with unchanged paired files and no unavailable
dependencies. The Lean SHA256 is
`089ae8481d71a254c643483f656eae1d71b8b0de2a33313f4692f5cafb1ee2b6`;
the Markdown SHA256 is
`53777096511731ee5e20702052c3ea90390543c4891090c3a83d20bfd2a4a1cf`.
Its full project definition closure consists of the accepted smooth-part
construction `9fb5627f-6e8c-48a5-a92f-a4ddcf319b2d`, version 1, and
foundational smoothness `665022df-625b-44ae-9dbd-425f6e266bab`, version 1.
All six effective dependency files match this workspace and its draft.
No universal-property or functoriality proof is imported.

The complete four-clause statement is one submission; its component lemmas
remain together in the adjacent draft proof. Statement acceptance does not
establish those laws as proved. The prepared environment is
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1, Lean 4.34.0 and Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435`.
