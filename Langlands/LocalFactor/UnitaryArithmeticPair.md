# Unitarity of the actual arithmetic local pairs

This internal derived construction transports supplied positive invariant
Hermitian forms to the actual local actions and tensor representations used in
arithmetic pair factors. It assumes unitarity of the original finite
representation; it does not infer unitarity of an automorphic representation.

`InvariantPositiveForm.diagonalTensor` retains the positive core of the
published external tensor form `InvariantPositiveForm.tensorProduct` and
restricts its invariance equation to `(g,g)`. Its carrier is the original
algebraic tensor and its action is exactly `Representation.tprod`. The pure
tensor inner product is the product of the two original inner products.
`FiniteRepresentation.isUnitary_tensor` repackages that form using the
published equivalence with `IsUnitarizable`. The Weil–Deligne adapter states
unitarity of the underlying action of the actual tensor pair; it imposes no
new condition on monodromy. The group and two carrier universes are independent.

For the relative Weil group, `localComponent_isUnitary` applies the published
restriction lemma to the supplied continuous local map. It keeps the original
carrier of the global representation. For every pair `A` satisfying
`IsBaseRestriction (localPairClass S ι) A`, the next lemma extracts its actual
local representative and the two genuine pair equivalences from the quotient
equality and the restriction datum. It transports the positive form through
these equivalences and the actual common-closure subgroup inclusion. This
proves unitarity for every admitted `A`, including carriers in an independent
universe. No representative is selected and no existence assertion is made.

The dual corollary first uses the published unitarity of the actual algebraic
contragredient of `S`. The final corollary applies the tensor lemma to every
pair of admitted representatives of the local classes of `S` and its dual.
Thus its tensor is exactly the one used by `conditionalPairEpsilonValue` and
`conditionalPairGammaValue` in an arithmetic self-pair datum.

The provenance is elementary restriction and transport of positive invariant
forms, together with the already published positivity of the tensor form.
These are internal consequences of existing Library constructions, with no
additional original-source assertion. The lemmas discharge the arithmetic
unitarity input to local Euler and gamma analysis. They do not establish
epsilon analyticity, supplied-pair gamma comparison, local automorphic
classification, block factor formulas, or the associated-pair induction
statement.

Author: Worker 1768.
