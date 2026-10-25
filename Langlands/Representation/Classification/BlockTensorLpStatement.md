# A common finite-exponent block tensor comparison

Authors: Worker 403 and Worker 158. This is an internal shared proof interface
for the two published analytic block tensor targets.

`Langlands.GLBlockTensorLpStatement.{uF,uV}` is a closed proposition. It asserts
that, for every real `r ≥ 2`, all irreducible admissible GL block factors satisfy
`T.IsLp (ρ i) r` if and only if their actual tensor satisfies
`IsLpModCenter (B.blockTensor ρ) μ r` for every Borel measurable-space realization
and every Haar measure on the actual product Levi quotient by its full center.
The module defines this proposition and proves no comparison.

The quantifiers reproduce the conventions of the unchanged
`BlockTensorAnalyticStatement` pair: every prime, actual p-adic field
`F : PadicField.{uF} p`, supplied compatible realization `T`, positive total
rank, ordered positive block shape, and actual family of representations on
arbitrary `Type uV` complex modules. The universes `uF` and `uV` are independent.
Irreducibility and the Library's all-open admissibility are explicit premises
on each factor. The field topology is `T.topology`; the Levi has the supplied
product topology `T.leviTopology B` and its proved topological group instance.
The tensor is exactly `B.blockTensor ρ = FiniteTensor.external ρ`.

On each factor, `T.IsLp` uses every Haar measure on the canonical Borel
measurable space of its actual central quotient. On the tensor side, the
measurable-space and Borel-space instances are quantified inside the right
side of the equivalence, followed by every Haar measure on that same actual
quotient. No scalar subgroup of the ambient GL group replaces the full Levi
center. The character witness in `IsLpModCenter` is existential and may depend
on the exponent and the measure. Its coefficients range over all vectors and
all actual smooth-dual functionals.

The real parameter is a finite real number; the coefficient predicate converts
it to the `MemLp` exponent with `ENNReal.ofReal`. The bound `r ≥ 2` is a
separate premise of the comparison. At `r = 2`, the already proved intrinsic
lemmas `isLpModCenter_two_iff` and `T.isLp_two_iff` identify its predicates with
the square-integrability predicates. For temperedness, a future proof can apply
the comparison at each `r = 2 + ε`, with `ε > 0`, and choose a character uniformly
in `ε` using the existing `UnitaryCentralCharacter.coefficientNorm_eq`.
Neither final analytic block comparison follows from this statement alone.

This is internally derived mathematical content, not a verbatim theorem
attributed to an original source. It isolates the common finite-exponent
argument described in the accepted `BlockTensorAnalyticStatement` Markdown,
using the published coefficient constructions and the new fixed-exponent
predicates. A proof must still establish the actual full-center quotient and
Haar transport, tensor central-character assembly and reflection, admissible
smooth-dual factorization, and product integration for all actual coefficients.
Reflection must use nonzero auxiliary coefficients on sets of positive finite
measure; restriction to a coordinate slice is insufficient. The comparison
assumes none of these steps as a certificate and uses no downstream induction,
classification, uniqueness or Jacquet-exponent criterion.
