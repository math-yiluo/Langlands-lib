# The twisted induced character formula from the local descent

Module `Langlands.BaseChange.TwistedInducedCharacterFormulaFromLocalDescent`.

`TwistedInducedCharacterFormulaFromLocalDescentStatement.{u, v, uW}` is the implication

`TwistedLocalDescentStatement.{u, v} → TwistedInducedCharacterFormulaStatement.{u, v, uW}`,

and `twistedInducedCharacterFormula_of_localDescent` proves it. The premise is stated, without
proof, in `Langlands.BaseChange.TwistedLocalDescentStatement`: near a σ-regular point, the
twisted constant term of a test function is a sum of test functions supported near the
twisted conjugacy classes of the Levi representatives `d j`, with masses
`|D_{G/M,σ}(d j)|_F^{-1/2} ∫ φ`. The conclusion is the twisted induced character formula of
Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en caractéristique non
nulle* (2011), II.4.5, formula (3) (printed p. 88), in the form of
`Langlands.BaseChange.TwistedInducedCharacterFormulaStatement`.

## Proof

`twistedInducedCharacterFormulaReduction` (module
`Langlands.BaseChange.TwistedInducedCharacterFormulaReduction`) proves
`TwistedVanDijkStatement → TwistedLocalDescentStatement → TwistedInducedCharacterFormulaStatement`,
and `TwistedVanDijk.twistedVanDijk` (module `Langlands.BaseChange.TwistedVanDijk.Proof`) proves
`TwistedVanDijkStatement`, the twisted van Dijk formula II.4.5 (2). Applying the first to the
second gives the theorem.
