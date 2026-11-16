# Inverse projection for commuting pullback squares

The shared theorem `Langlands.GroupScheme.Descent.squareComparison_inv_fst_fst`
states that the inverse of the canonical comparison between two iterated
pullbacks preserves their projection to the original group scheme. It applies
to arbitrary schemes in one universe, four maps forming a commuting square,
and an actual group scheme over the bottom base. Its reassociated form is
available as `squareComparison_inv_fst_fst_assoc`.

The proof expands `squareComparison` and uses the existing forward and inverse
projection formulas for `pullbackComparison`. This is the unchanged theorem
formerly declared in `IntegralModel.TwistCoefficientComparison`, shared with
`Descent.LocalSolutionComparison` to avoid duplicate declarations. Both
consumers retain its full name and mathematical statement. It introduces no
additional hypotheses or mathematical result.
