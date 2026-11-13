# Contragredient, twist and character compatibility of the relative generated isometry

This module proves the published proposition
`Langlands.Global.PoleComparison.RelativeIsometryOperationStatement.{uF, uW, uP}`
(module `Langlands.Global.Factors.RelativeIsometryOperationStatement`) as the theorem

`Langlands.Global.PoleComparison.relativeIsometryOperation :
  RelativeIsometryOperationStatement.{uF, uW, uP}`.

The universes `uF`, `uW` and `uP` are arbitrary. The theorem keeps every quantifier and
hypothesis of the published statement and adds none. It covers every Galois extension
`E / F` of number fields with compact adele quotient, every arithmetic class family `c`,
every finite place `v`, every nontrivial additive character `ψ`, every certified pole
comparison and every generated positive isometry `T`. Its conclusion is
`RelativeIsometryOperations F E c v T`: `T` is compatible with contragredients, with twists by
modulus-one characters and with rank-one characters.

## Implemented proof

The proof is one application of the published conditional reduction
`Langlands.Global.PoleComparison.relativeIsometryOperationStatement_of_globalInputs`
(module `Langlands.Global.Factors.RelativeIsometryOperationReduction`). That theorem derives
the target from eleven global propositions. This module supplies each of them as an
already published proved theorem, so no proposition is assumed:

| Reduction input | Published proposition | Theorem used | Module |
| --- | --- | --- | --- |
| `hrec` | `Langlands.LocalClassField.WeilReciprocityExistenceUniqueness.{uF}` | `Langlands.LocalClassField.geometricWeilReciprocityExistenceUniqueness` | `Langlands.ClassFieldTheory.Local.WeilReciprocityExistenceProof` |
| `hmap` | `Langlands.ClassField.Global.LocalRelativeWeilMapExistenceStatement.{uF}` | `Langlands.ClassField.Global.localRelativeWeilMapExistence` | `Langlands.ClassField.Global.LocalRelativeWeilMapExistenceProof` |
| `hcentral` | `Langlands.ClassField.Global.RelativeWeilGroup.AssociatedCentralCharacterStatement.{uF, uW, uP}` | `Langlands.ClassField.Global.RelativeWeilGroup.associatedCentralCharacter` | `Langlands.Automorphic.AssociatedCentralCharacterProof` |
| `hdual` | `Langlands.Automorphic.CuspidalUnitaryContragredientExistenceStatement.{uF}` | `Langlands.Automorphic.cuspidalUnitaryContragredientExistence` | `Langlands.Automorphic.CuspidalUnitaryContragredientExistenceProof` |
| `hdualpres` | `Langlands.Automorphic.CuspidalContragredientPresentationExistenceStatement.{uF, uP, uP}` | `Langlands.Automorphic.cuspidalContragredientPresentationExistence` | `Langlands.Automorphic.CuspidalContragredientPresentationExistenceProof` |
| `hduallocal` | `Langlands.Automorphic.CuspidalContragredientLocalCompatibilityStatement.{uF, uP, uP}` | `Langlands.Automorphic.cuspidalContragredientLocalCompatibility` | `Langlands.Automorphic.CuspidalContragredientLocalCompatibilityProof` |
| `hdualassoc` | `Langlands.ClassField.Global.RelativeWeilGroup.PresentedContragredientAssociationStatement.{uF, uW, uP, uP}` | `Langlands.ClassField.Global.RelativeWeilGroup.presentedContragredientAssociation` | `Langlands.Automorphic.Unramified.ContragredientAssociation` |
| `htwist` | `Langlands.Automorphic.CuspidalDeterminantMultipleStatement.{uF, uP}` | `Langlands.Automorphic.cuspidalDeterminantMultiple` | `Langlands.Automorphic.CuspidalDeterminantMultipleProof` |
| `htwistassoc` | `Langlands.ClassField.Global.RelativeWeilGroup.PresentedDeterminantMultipleAssociationStatement.{uF, uW, uP, uP}` | `Langlands.ClassField.Global.RelativeWeilGroup.presentedDeterminantMultipleAssociation` | `Langlands.Automorphic.HeckeDeterminantTwistAssociationProof` |
| `htransfer` | `Langlands.ClassField.Global.RelativeWeilGroup.LocalTransferReciprocityStatement.{uF}` | `Langlands.ClassField.Global.RelativeWeilGroup.localTransferReciprocity` | `Langlands.ClassField.Global.LocalRelativeWeilTransferProof` |
| `hextend` | `Langlands.Global.UnitaryLocalCharacterExtensionStatement.{uF}` (unfolded in the reduction) | `Langlands.Global.unitaryLocalCharacterExtension` | `Langlands.Global.Arithmetic.UnitaryLocalCharacterExtensionProof` |

Each theorem in the third column is applied at the universe instance that the reduction
requires; Lean infers these instances from the reduction's parameter types. The new
mathematics is in the reduction and in the eleven imported proofs. This module only
composes them. In outline, local reciprocity existence and uniqueness and local relative
Weil map existence give a characterized local-map family, and the reduction shows that `T`
fixes every witnessed generator pair. Dual closure of the witnessed generators comes from the central-character
comparison and the four contragredient inputs. Twist closure comes from the
determinant-multiple inputs, local transfer reciprocity and the extension of unitary
local characters to unitary Hecke characters. The rank-one character case is twist closure
applied to the trivial witnessed generator. The Markdown of
`Langlands.Global.Factors.RelativeIsometryOperationReduction` describes these steps.

## Checks

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`. It adds no
hypothesis and no new axiom, and it leaves the target pair and every pair it imports
unchanged. It takes no local Langlands result as a hypothesis: its only inputs are the
published theorems listed above, and none of them depends on this target.

## Provenance

This proof contains no new mathematical argument and cites no source literature for it.
Its correctness rests on the published reduction and the eleven published proofs listed
above, which give their own provenance.
