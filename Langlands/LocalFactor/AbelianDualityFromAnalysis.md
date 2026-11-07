# Scalar duality from Tate local analysis

`NonabelianSystem.AbelianDualityFromLocalAnalysisStatement` is the implication
from the existing `PadicAbelianLocalAnalysisStatement` to the existing
`AbelianExpressionDualityStatement`, with the full field universe `uF`.
`abelianDualityFromLocalAnalysis` proves this implication. The analytic premise
remains explicit.

For each prime, actual common-closure intermediate field, continuous field
quasicharacter `chi`, nontrivial unitary additive character `psi`, and supplied
regular Haar measures `mu, mu'` satisfying exactly `FourierDualMeasures`, the
conclusion is

```text
epsilonExpression(chi, psi, mu) *
  epsilonExpression(normalizedAbsCharacter * chi^-1, psi.scale(-1), mu') = 1.
```

The expressions are the previously constructed actual abelian epsilon
expressions. The proof preserves their fields, characters, conductors and
measures.

Two elementary helpers show that the normalized absolute-value character has
conductor zero and its value on the chosen uniformizer is the spectral variable
at one. The first uses the characterization of conductor zero by triviality on
the actual units; the second uses the residue-normalized absolute-value
formula and the real exponential-log identity.

For the main proof, put `a = multiplicativeConductor chi` and
`n = additiveConductor psi`. The conductor-operation clause of the supplied
local-analysis statement gives conductor `a` for both `chi^-1` and
`normalizedAbsCharacter * chi^-1`. Scaling `psi` by minus one preserves `n`,
and the resulting underlying additive character is exactly the inverse of
`psi.toAddChar`.

`fourierDualIntegerVolume` converts the unchanged Fourier-dual premise to the
actual volume product `vol(O) * vol'(O) = q^(-n)`. The dual-Haar clause of
local analysis, applied at spectral parameter zero, then gives the product of
`epsilonAt(chi, psi, mu, 0)` and
`epsilonAt(chi^-1, psi^-1, mu', 1)` equal to one.
The unramified-twist clause, applied to `chi^-1`, the inverse additive character,
`mu'`, and the normalized absolute-value character at shift one, identifies
the second factor with the norm-twisted inverse character's epsilon at zero.
The proved conductor identities identify these explicit-conductor expressions
with the constructed epsilon functions. Finally,
`deligneConstant_eq_abelianEpsilonExpression` converts both zero-parameter values
to the actual abelian expressions.

`dualFunctionalEquation_of_generation_of_localAnalysis` composes this result
with the existing actual character-line adapter and generation assembly. It
retains two explicit premises:
`CommonClosureDegreeZeroGenerationStatement.{uF,uV}` and
`PadicAbelianLocalAnalysisStatement.{uF}`. Its conclusion is exactly the unchanged
`DualFunctionalEquationStatement.{uF,uV}`, with independent representation
universe `uV`. This module proves neither of those two premises and does not
complete the unconditional host proof task.

This is an internal interface derivation from the published statement clauses,
the Fourier-volume adapter, the actual conductor constructions and the
previously proved conditional assembly. It claims no additional original
analytic result or literature theorem.
