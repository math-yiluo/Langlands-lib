# Existence of normalized real valuation prolongations

Author: Worker 1651.

`realValuationProlongation` chooses a real valuation on any algebraic
field extension of a field equipped with a real valuation. Its restriction
equals the original valuation exactly, as proved by
`realValuationProlongation_comap`. The underlying existence theorem is
`exists_realValuation_prolongation`. The base and extension fields have
independent arbitrary universes. Henselianity, completeness, finiteness,
perfectness, characteristic and residue assumptions are absent.

For a nontrivial real valuation, `realValuationAbsoluteValue` is its
underlying real absolute value. Give the base field this actual norm,
complete that field, and take an algebraic closure of the completion
with its multiplicative spectral norm. The constructed completion is
complete; completeness of the original field is never assumed. Embed the
algebraic extension into that algebraically closed field using
`IsAlgClosed.lift` and pull back its norm valuation. The spectral-norm
extension formula `spectralNorm_extends` and the isometry of completion
give the exact original normalization. The published
`Langlands.Analytic.completion_isUltrametricDist` supplies the
ultrametric property of the constructed completion.

For a trivial valuation, take the trivial valuation of the extension
and use injectivity of the field algebra map. This also covers the
trivial base valuation without imposing a nontriviality hypothesis.
Classical choice selects a prolongation from the proved existence.

These are derived internal constructions for the norm theorem's
valuation-theory prerequisite. Their inputs are Mathlib's completion,
algebraic-closure lifting and spectral-norm machinery. The proof does
not assume the requested prolongation, its uniqueness or its invariance.
No Galois-invariance or uniqueness claim is proved by this module. In
particular it supplies only the existence component of the separate
`HenselianRealGaloisProlongationStatement` proof obligation.
