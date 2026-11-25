# Smooth-part linear factorization laws: proposition target

`Langlands.SmoothHomLawsStatement` is a proposition definition
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
context and exact smooth-part dependency are documented in
[HomDefinitions](HomDefinitions.md), with Casselman Chapter II, Section 1,
page 2, first two paragraphs, literature ID
`casselman-2019-smooth-representations`, SHA
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
They are not presented as quotations of a numbered source theorem.

This module defines the target without assuming or proving its clauses. Its
sole direct construction import is `HomDefinitions`. The preparation
record reports unchanged paired files and no unavailable dependencies. The
recorded Lean SHA256 is
`089ae8481d71a254c643483f656eae1d71b8b0de2a33313f4692f5cafb1ee2b6`;
the recorded Markdown SHA256 is
`53777096511731ee5e20702052c3ea90390543c4891090c3a83d20bfd2a4a1cf`.
Its full project definition closure consists of the smooth-part
construction `Langlands.Representation.Smooth.SmoothPart.Definitions` and
foundational smoothness `Langlands.Representation.Smooth.Definitions`.
The preparation record reports that all six dependency files matched.
No universal-property or functoriality proof is imported.

The complete four-clause target is proved by `Langlands.smoothHomLaws` in
`HomProof.lean`, with its component lemmas in that module. The preparation
environment is Lean 4.34.0 and Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435`.
