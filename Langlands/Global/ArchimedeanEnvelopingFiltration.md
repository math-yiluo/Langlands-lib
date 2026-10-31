# Degree filtration on the actual archimedean enveloping algebra

Author: Worker 94. This is an internal specialization of
`Langlands.Algebra.UniversalEnvelopingFiltration` to the published actual
complexified archimedean matrix Lie algebra. It applies to `K : Type u`
with a field structure and every `n : ℕ`; finite-dimensionality of the
pieces additionally uses `NumberField K`. No positive-rank condition is
imposed.

`envelopingDegreeOne` is the sum of the scalar submodule and the actual
canonical Lie-generator image inside `EnvelopingAlgebra K n`.
`envelopingDegreeFiltration K n d` is its `d`th submodule power, and
`envelopingDegreeFiltrationLT` is the supremum of smaller-index pieces.
These are aliases for the generic construction, so its graded
multiplication and `IsRingFiltration` instances apply directly.

The specialized theorems establish monotonicity, exact multiplication
of pieces with indices `p` and `q` into the piece `p+q`, membership of
the actual `envelopingGenerator` in degree one, exhaustivity, and the
commutator bound in degree `p+q-1` with natural-number subtraction.
The generic proof uses the defining Lie commutator relation and
product induction, including scalar degree-zero cases.

For a number field, the actual real matrix space has finite dimension.
The published linear equivalence `realLieAlgebraToMatrix` transfers this
to `RealLieAlgebra K n`. Mathlib's finite-module base-change instance
gives finiteness of `ComplexLieAlgebra K n` over `ℂ`. The generic finite
power theorem then gives `envelopingDegreeFiltration_finite` for every
degree. The real algebra includes both real directions at complex
places, and its complexification is the actual published tensor product.

This establishes finite degree pieces of the actual enveloping algebra.
PBW, symmetrization, generation over its center, admissibility, analytic
regularity and the final automorphic differential-growth theorem remain
separate obligations.
