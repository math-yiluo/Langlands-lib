# Rigidified classes under dual base change

This module shares the five class-comparison helpers formerly private in
[DualAbelianBaseChangeProof](DualAbelianBaseChangeProof.md). Their bodies and
hypotheses are unchanged; they use the public names introduced in the reviewed
[FiniteWeilBaseChange](FiniteWeilBaseChange.md) contribution.

- `rigidifiedClassesBaseChange` maps rigidified line-bundle classes by the
  actual family base-change functor. Its naturality and tensor lemmas compare
  parameter pullback and tensor product respectively.
- `classifyingMap_baseChangeFamily` identifies classification by a base-changed
  family with the base change of its classified class.
- `dualPointClass_dualSchemeBaseChangeIso` applies that identity to the
  Poincare family and its prescribed comparison.

The tensor identity retains its preservation, composition and left-unit
coherence assumptions. The dual-point identity retains Picard-zero pullback
stability and base-change universality. These helpers do not assert
unconditional dual existence or any new geometric property.
