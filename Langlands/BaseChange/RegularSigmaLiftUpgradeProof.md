# Proof that the regular σ-lift identity implies the σ-lift identity

`Langlands.BaseChange.regularSigmaLiftUpgrade` proves
`RegularSigmaLiftUpgradeStatement.{u, v, uV, uW}` at all four universe parameters. Its
eight premises remain premises.

## Proof

After introducing the premises, the base data `F`, `E`, `σ`, `l`, `n`,
`hE : IsCyclicAlgebra σ l` and the topological instances on `GL_n(F)` and `GL_n(E)`, take
irreducible admissible `π` and `τ`, an intertwiner `A`, a constant `c` and
`IsRegularSigmaLift σ l π hπ τ hτ A c`. The proof has two steps.

1. `SigmaLiftCharacterIdentity.isShintaniLift_of_isRegularSigmaLift` (module
   `Langlands.BaseChange.SigmaLiftCharacterIdentity.RegularForward`) gives
   `IsShintaniLift σ l π hπ τ hτ A c` from the first five premises:
   `TwistedCharacterRegularValuesStatement` at `{u, u, uV}` and at `{u, v, uW}`,
   `RegularTransferStatement`, `ConcordantIntegralEqualityStatement` and
   `SigmaLiftCharacterIdentity.SigmaRegularOpenStatement`. It reruns the forward argument
   of `sigmaLiftCharacterIdentityForward`. It also cuts the transferred ordinary test
   function by the condition that its determinant is a norm, which keeps concordance
   (module `Langlands.BaseChange.SigmaLiftCharacterIdentity.NormDeterminantCutoff`). So the
   trace identity is needed only on pairs allowed by `IsRegularSigmaLift`.
2. `sigmaLiftCharacterIdentityReverse` (module
   `Langlands.BaseChange.SigmaLiftCharacterIdentityReverse`) gives
   `IsSigmaLift σ l π hπ τ hτ A c` from the Shintani identity and the last three premises:
   `ConcordantIntegrableIntegralEqualityStatement`, `CharacterLocalIntegrabilityStatement`
   and `TwistedCharacterLocalIntegrabilityStatement`.

The proof uses no statement about the existence of descents or lifts. It uses neither
`SigmaDiscreteDescentStatement` nor `SigmaDiscreteRegularDescentStatement`, and neither
`CuspidalSigmaLiftExistenceStatement` nor `LocalCyclicBaseChangeStatement`.
The module `Langlands.BaseChange.SigmaDiscreteRegularDescentStatement` is imported only
for the definition of `IsRegularSigmaLift`.

## Sources

- Guy Henniart and Bertrand Lemaire, *Changement de base et induction automorphe pour
  GLₙ en caractéristique non nulle*, Mém. SMF 124 (2011): II.2.9 (printed pp. 69–71,
  PDF pp. 77–79), the equivalence of the σ-lift and the Shintani identity, and II.6.13
  (printed pp. 129–130, PDF pp. 137–138), the σ-lift from the trace identity on
  regularly supported concordant pairs. Source ID
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`.
- James Arthur and Laurent Clozel, *Simple Algebras, Base Change, and the Advanced Theory
  of the Trace Formula*, Annals of Mathematics Studies 120 (1989): Chapter 1, §6.3 (printed
  p. 57, PDF p. 71). Source ID `arthur-clozel-1989-base-change`.
