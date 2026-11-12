# Contragredient association for actual cuspidal realizations and classes: proof

Module: `Langlands.Automorphic.Unramified.ContragredientAssociationProof`. Author: Worker 5016.

`Langlands.ClassField.Global.RelativeWeilGroup.associatedContragredient` proves the published
proposition `Langlands.ClassField.Global.RelativeWeilGroup.AssociatedContragredientStatement.{u, uV, uP, uQ}`
of [AssociatedContragredientStatement](../AssociatedContragredientStatement.md), at all four
independent universe levels. That proposition is the conjunction of the presented form
`PresentedContragredientAssociationStatement.{u, uV, uP, uQ}` and the class form
`ClassContragredientAssociationStatement.{u, uV, uP, uQ}`: if a cuspidal realization (or class)
is weakly associated with a continuous Weil representation `S`, then its supplied full-operator
contragredient is weakly associated with the dual `S.dual`.

## The implemented proof

The theorem is the pair of two published results.

1. The presented form is `presentedContragredientAssociation`
   ([ContragredientAssociation](ContragredientAssociation.md)): at each unramified place the dual
   local components are unramified and their Euler polynomials are those of the inverse transposes,
   which match the dual Weil representation.
2. The class form is `classContragredientAssociation_of_dualPresentationExistence`
   (same module) applied to `Langlands.Automorphic.cuspidalDualPresentationExistence`
   ([CuspidalDualPresentationExistenceProof](../CuspidalDualPresentationExistenceProof.md)), the
   proof of `CuspidalDualPresentationExistenceStatement.{u, uP, uQ}`. The latter supplies a
   presentation of the contragredient in the output universe `uQ`, to which the presented form
   applies.

No hypothesis is added; neither unitarity nor admissibility of the realizations is assumed.
