# Finite triangular translations of product measures

Author: Worker 117.

This module states the internal prerequisite
`Langlands.HarmonicAnalysis.FiniteTriangularTranslationStatement`. It supplies
no proof. The declaration is a transparent proposition definition.

Let `ι` be any finite index type and let `X i` be measurable additive commutative
groups, with jointly measurable addition. For each index let `μ i` be a
sigma-finite measure invariant under every left translation. No topology, Haar
normalization, or nonzero-measure assumption is imposed. Give the dependent
product `∀ i, X i` its product measurable structure and product measure
`Measure.pi μ`.

Choose any natural-valued rank function on the indices and a measurable map
`f` from the product to itself. Assume that `f x i` depends only on coordinates
of rank strictly smaller than `rank i`: whenever `x` and `y` agree in every such
coordinate, `f x i = f y i`. The proposition says that

`x ↦ (fun i => f x i + x i)`

preserves `Measure.pi μ`. In particular its pushforward is the same product
measure. Distinct coordinates may have equal rank; their translation terms
cannot depend on each other. The empty index type is included. The index and
coordinate universes are independently quantified.

## Internal provenance and intended application

This is a finite-product measure lemma isolated for the proof of
`Langlands.GLBlockModulusHaarStatement`. It is not a transcription of a
literature theorem. The intended proof is by successive coordinate translations
(or finite-product integration), using only translation invariance and the
strict rank dependence. Proving that argument is a separate obligation.

For upper block unipotent coordinates `x_ij` with `i < j`, multiplication on
the left by a fixed element with coordinates `a_ij` has the expected form

`x_ij ↦ a_ij + x_ij + ∑_{i<k<j} a_ik * x_kj`.

Assign coordinate `(i,j)` rank `j-i`. Every variable `x_kj` in the translation
term has strictly smaller rank. Rectangular matrix spaces are additive
commutative groups, so the proposition is suited to this situation. This
paragraph explains the internal motivation; this module neither constructs
the block coordinates nor proves their multiplication formula. Applying the
proposition will still require that formula, measurable dependence, suitable
coordinate measures, and transport to the actual unipotent group. The
proposition also does not compute the scaling of any Levi action.
