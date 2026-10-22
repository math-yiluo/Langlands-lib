# Proof of completed residue-field evaluation

Author: Worker 36.

`Langlands.Analytic.completedResidueFieldProperties` proves the separate
proposition `Langlands.Analytic.CompletedResidueFieldStatement`.
The constructed field and maps are imported from the separate
Definitions module. The original ResidueField import path continues to
expose their names and the existing evaluation lemmas.

The norm of a completed image equals the norm of its residue-fraction-field
representative by Mathlib's completion norm identity. The construction's
fraction-field norm identity then gives exactly x(a). An image is zero
exactly when its norm is zero, so this equality identifies its zero fiber
with the original seminorm kernel. Extensionality of spectrum points
turns the same norm identity into the claimed pullback equality.

The ring map from the normed residue fraction field is definitionally the
canonical inclusion into its actual metric completion. Mathlib's
completion isometry and dense-range theorems therefore prove the last two
clauses. The closing theorem assembles all five properties with the
statement's independent universes and unchanged hypotheses.

The proof does not assume completeness of the coefficient field or source
algebra and asserts density of the fraction field, not density of A.
The source conventions and derived generality are documented in the
paired ResidueField/Definitions and ResidueField/Statement Markdown.
