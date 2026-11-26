# σ-lift induction from the σ-lift/Shintani equivalence and the twisted character formula

`SigmaLiftInductionTwistedFormulaReductionStatement.{u, v, uV, uW}` is the
proposition

```text
SigmaLiftCharacterIdentityStatement.{u, v, uV, uW} →
SigmaLiftCharacterIdentityStatement.{u, v, max u uV, max v uW} →
TwistedInducedCharacterFormulaStatement.{u, u, uV} →
TwistedInducedCharacterFormulaStatement.{u, v, uW} →
SigmaLiftInductionStatement.{u, v, uV, uW}
```

and `sigmaLiftInduction_of_twistedFormula` proves it for all four universes.
The four premises are explicit Lean propositions of the Library; this module
proves none of them. The conclusion is the Library's statement of
Henniart–Lemaire (2011), II.4.4, Lemme (printed p. 85, PDF p. 93), with the
existential intertwiner and the constant `∏ i, c i`.

## The premises

- `SigmaLiftCharacterIdentityStatement` is Henniart–Lemaire, II.2.9,
  Proposition (printed p. 69): for irreducible admissible `π` and `τ`, a
  σ-intertwiner `A` and `c : ℂ`, `IsSigmaLift` (identity of distributions on
  concordant test functions) is equivalent to `IsShintaniLift` (identity of
  character values at associated regular points). It is used at the universes
  `uV`, `uW` of the factors and at the universes `max u uV`, `max v uW` of the
  carriers of the normalized product inductions.
- `TwistedInducedCharacterFormulaStatement` is the twisted case of
  Henniart–Lemaire, II.4.5, formula (3) (printed p. 88, PDF p. 96): the twisted
  character value of the normalized product induction, for the induced
  intertwiner `ι(A)`, at `δ` norm associated with a regular semisimple `γ`, is
  `∑ j, |D_{G/M}(m j)|_F^{-1/2} * b j` over a Levi class system `m` for `γ`,
  with the twisted Levi values `b j`. It is used at universes `{u, v, uW}`
  (the representations over `E`) and `{u, u, uV}` (the representations over
  `F`, in degree one).

## Proof implemented in Lean

The proof is the composition of three theorems of the Library:

1. `inducedCharacterFormula_of_twisted`
   (`Langlands.BaseChange.InducedCharacterFormulaFromTwisted`) turns the
   premise `TwistedInducedCharacterFormulaStatement.{u, u, uV}` into
   `InducedCharacterFormulaStatement.{u, uV}`, the ordinary formula (3), by
   specializing to `E = F`, `σ = 1`, `l = 1` with identity intertwiners.
2. `sharedInducedCharacterExpansion_of_formulas`
   (`Langlands.BaseChange.SharedInducedCharacterExpansionFromFormulas`) turns
   the ordinary formula and `TwistedInducedCharacterFormulaStatement.{u, v, uW}`
   into `SharedInducedCharacterExpansionStatement.{u, v, uV, uW}`: common finite
   expansions, with the same coefficients and associated block arguments, of
   the ordinary and twisted induced characters at associated regular pairs.
3. `sigmaLiftInductionReduction`
   (`Langlands.BaseChange.SigmaLiftInductionReduction`) derives
   `SigmaLiftInductionStatement.{u, v, uV, uW}` from the two instances of
   `SigmaLiftCharacterIdentityStatement` and the shared expansion: the factor
   σ-lifts become Shintani identities, the expansions compare the induced
   characters with the factor `∏ i, c i`, and the reverse direction of the
   equivalence for the induced representations, with the induced intertwiner
   `inducedSigmaIntertwiner σ B A` and the admissibility proofs
   `isAdmissible_normalizedProductInduced`, gives the σ-lift.
