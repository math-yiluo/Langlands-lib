# The global functional equation for twisted relative Weil pairs

Lean module: `Langlands.Global.Factors.RelativeWeilFunctionalEquationProof`
(namespace `Langlands.Global.FunctionalEquationComparison`).

Author: Worker 5014 (task `cc3ec74b-6eb5-4fd8-af55-97f37ce4d76c`).

## Statement proved

`relativeWeilTwistFunctionalEquation : RelativeWeilTwistFunctionalEquationStatement.{u, uV, uE}`

This proves exactly the published proposition
`Langlands.Global.FunctionalEquationComparison.RelativeWeilTwistFunctionalEquationStatement.{u, uV, uE}`
of the module `Langlands.Global.Factors.RelativeWeilFunctionalEquationStatement`, with all
three universes free. The theorem has no hypotheses. The statement module and the modules
it imports are unchanged. The statement's own Markdown gives the meaning of the proposition.

The axioms used are `propext`, `Classical.choice` and `Quot.sound`.

## Source

John Tate, *Number theoretic background*, Proc. Sympos. Pure Math. 33, Part II (1979),
3–26 (registered `tate-1979-number-theoretic-background`), Theorem (3.5.3) and the
paragraph after it, p.16. Guy Henniart, *Une preuve simple des conjectures de Langlands
pour GL(n) sur un corps p-adique*, Invent. Math. 139 (2000), §2.3 (registered
`henniart-2000-simple-proof`), uses these functional equations for twisted pairs.

## Proof

The proof is one line:

`relativeWeilTwistFunctionalEquation_of_localTransferReciprocity
  ClassField.Global.RelativeWeilGroup.localTransferReciprocity.{u}`.

1. `relativeWeilTwistFunctionalEquation_of_localTransferReciprocity`, in the companion
   module `Langlands.Global.Factors.RelativeWeilFunctionalEquationAssembly` (submitted with
   this proof), derives the target from
   `ClassField.Global.RelativeWeilGroup.LocalTransferReciprocityStatement.{u}`. Its Markdown
   gives the full argument. In short, it follows Tate's proof of (3.5.3): Brauer's theorem
   writes each twist of the class of `S ⊗ S'` as an integral combination of representations
   induced from characters of intermediate fields. The local restriction formula, local
   transfer reciprocity and class field theory identify the local factors at each finite
   place with products of Hecke local factors. The Hecke functional equations then give the
   global functional equation. The whole archimedean block is placed at one infinite place.
   This is allowed because the target's archimedean block is existential.
2. `Langlands.ClassField.Global.RelativeWeilGroup.localTransferReciprocity :
   LocalTransferReciprocityStatement.{u}` (module
   `Langlands.ClassField.Global.LocalRelativeWeilTransferProof`) is the published
   unconditional proof of local transfer reciprocity.

## Public theorems used

- `Langlands.ClassField.Global.RelativeWeilGroup.localTransferReciprocity`.
- Through the companion module: among others,
  `Langlands.ClassField.Global.RelativeWeilGroup.localInducedRestriction`,
  `Langlands.LocalClassField.commonClosureGeometricProof`,
  `heckeGlobalFunctionalEquation_proof`, `hasGlobalEquation_brauerProduct`,
  `inducedCharacterGeneration`, `transferCharacterFactorization` and
  `transferNormCompatibilityStatement`. The companion Markdown lists them with their roles.
