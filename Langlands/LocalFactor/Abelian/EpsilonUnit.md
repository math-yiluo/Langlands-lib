# Units and Haar-independent abelian epsilon ratios

Worker 1727 derives these constructions from the published actual Tate local
analysis. They use the original `TopologicalData.abelianEpsilonExpression`;
neither the integral nor its normalization is changed.

For every finite p-adic field, supplied topological realization, continuous field
quasicharacter, nontrivial unitary additive character and regular additive Haar
measure, `abelianEpsilonExpression_ne_zero` identifies the expression with the
published spectral expression at zero and applies the proved
`PadicAbelian.epsilonAt_ne_zero`. That theorem is part of the proof development
of `PadicAbelianLocalAnalysisProof`. Its hypotheses are discharged with the
published specifications of the actual multiplicative and additive conductors.

`abelianEpsilonUnit` is `Units.mk0` of precisely this expression with the resulting
nonvanishing proof. Its coercion lemma is definitional.

`abelianEpsilonExpression_haarScale` uses the same identification at zero and the
proved spectral Haar scaling formula. `abelianEpsilonUnit_haarScale` lifts this
identity by injectivity of the coercion from complex units.

`abelianEpsilonRatio` divides the unit for one character by that for a second
character, with the same additive character and Haar measure.
`abelianEpsilonRatio_haarScale` cancels the common positive factor.
`abelianEpsilonRatio_haarIndependent` uses Mathlib's uniqueness of regular
additive Haar measures: the first measure is a positive finite real multiple of
the second. It then applies the scaling result. Proof fields of the Haar
structures are propositions, so equality of their measures gives equality of
the structures.

These are internal supporting constructions for descent of abelian values to
degree-zero exact virtual representations. They do not assert compatibility
with any Brauer relation, construct a nonabelian system, or prove existence.
The source normalization and provenance are those of the unchanged
[`Definitions.md`](Definitions.md),
[`GaussEpsilon.md`](GaussEpsilon.md), and
[`GaussDual.md`](GaussDual.md). All field universes are retained.
