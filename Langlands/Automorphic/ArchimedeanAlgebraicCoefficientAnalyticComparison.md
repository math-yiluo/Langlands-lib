# Actual analytic and algebraic archimedean coefficient comparison

This internal adapter specializes the published comparison of the genuine
scheme representation's real Fréchet derivative with its dual-number
differential. Specifically,
`MatrixRepresentation.analyticProductDifferentialComparison` supplies the
premise of the previously conditional
`analyticRealDifferential_eq_lie_of_comparison` for the original `ρ` and the
test algebra `ℂ`. The new `analyticRealDifferential_eq_lie` has no comparison
premise and applies to every real Lie vector and every original coefficient
vector.

`analyticComplexDifferential_eq_lie` extends the equality to the entire
complexified Lie algebra by tensor induction. On `z ⊗ X`, both actions are
the complex scalar `z` times their equal real-direction actions.
Additivity handles sums. `analyticComplexLieAction_eq` consequently identifies
the two independently constructed Lie homomorphisms into coefficient
endomorphisms.

`analyticAlgebraicLieEquiv` equips the existing identity coordinate
equivalence from `AnalyticSpace e ρ` to `Space e ρ` with this proved Lie
compatibility. It retains every original vector. The full group representations
already use the same original scheme-point action; the same coordinate identity
therefore gives `analyticAlgebraicRepresentationEquiv` and its full compact
restriction `analyticAlgebraicCompactEquiv`. Their application lemmas identify
their underlying maps with that of the Lie equivalence. The last two theorems
prove compatibility with the actual reduced and compact Lie restrictions by
applying the full Lie equivalence to their respective inclusion maps.

The number-field universe remains independent of the small finite selected
embedding and coefficient indices. Both complex-place orientations, all
coefficient vectors, empty indices and rank zero are retained. The real and
complex differential equality lemmas do not require the `NumberField`
instance. The analytic module and representation comparisons are stated in
the existing number-field coefficient framework.

The provenance is internal specialization and scalar extension of the published
generic comparison proof and the existing coefficient constructions. This pair
does not claim a new original-source definition or comparison theorem.
