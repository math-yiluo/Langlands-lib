# Proof of the zero-dimensional uniform Lang–Weil estimate

Worker 107.

This derived proof imports the unchanged published statement
`Langlands.AlgebraicGeometry.LangWeil.FamilyLangWeilZeroStatement`.
Its mathematical inputs are the Library's pure-dimension-zero comparison
in `RelativeDimensionLoci` and Mathlib's quasi-finite, geometric
irreducibility, universally injective, purely inseparable and perfect-field
results.

Every residue-field fibre of a geometrically irreducible locally quasi-finite
morphism is irreducible and discrete, so has at most one point. These properties
persist after arbitrary base change, giving universal injectivity. Mathlib's
universal-injectivity criterion then gives both injectivity on field-valued
points and purely inseparable residue field extensions.

For a point of the base valued in a perfect field, surjectivity of the original
morphism supplies a point above its image. The embedding of the base residue
field into the perfect field extends across the purely inseparable residue
field extension. The corresponding spectrum morphism lifts the given
field-valued point. Thus the map on perfect-field-valued points is bijective.

Pure dimension zero gives local quasi-finiteness by the published comparison
`SchemeFiberGeometry.hasPureDimensionFibers_zero_iff_locallyQuasiFinite`.
Finite fields are perfect, so the lift type in the target has cardinality
exactly one. Its error from the dimension-zero main term is zero. Choosing the
positive uniform constant `1` proves `familyLangWeilZero` with exactly the
published target and no additional hypotheses. The proof does not need the
target's quasi-compactness and arithmetic-base hypotheses.

The dimension-zero interpretation and its provenance are documented in the
imported statement's paired Markdown. This implementation follows the
elementary residue-field argument, without a positive-dimensional Lang–Weil
estimate.
