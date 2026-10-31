# Opposite cuspidal Jacquet length and multiplicity inside a product Levi

Module `Langlands.Representation.Classification.ProductLeviCuspidalJacquetMultiplicityProof`.
Theorem `Langlands.productLeviCuspidalJacquetMultiplicity`.

## Statement

The theorem proves `Langlands.ProductLeviCuspidalJacquetMultiplicityStatement.{uF,uV,uW}`
(module `Classification/ProductLeviCuspidalJacquetMultiplicityStatement`). Its type is
exactly that proposition, with independent universes for the field, the inducing carrier
and the comparison carrier.

Informally: take a prime `p`, a `p`-adic field `F` with compatible topological data `T`,
a positive rank `n`, a coarse block shape `B` of `n`, a refinement `S` of `B`, and the
fine shape `C = B.flatten S`. Let `σ` be an irreducible cuspidal representation of
`C.Levi`. Transport `σ` along the inverse of `flattenedLeviEquiv F B S`, induce it with
the normalized refined induction `normalizedRefinedInduced B S`, and take the normalized
refined opposite Jacquet module `normalizedRefinedOppositeJacquet B S`. This module has
a composition series whose length is the number of minimal self-conjugating permutations
in `MinimalConjugatingPermutations C C` that lie in `blockWeyl B`. Let `τ` be an irreducible
representation of `C.Levi`, transported in the same way. For every natural number `m`,
`τ` occurs with Jordan–Hölder multiplicity `m` if and only if `m` is the number of
associating permutations of `AssociatingPermutations C C σ τ` that lie in `blockWeyl B`.

This is the product-Levi specialization of Silberger 1979, Theorem 5.4.1.1 (printed
pp. 287–288), and of Bernstein–Zelevinsky 1977, Corollary 2.13(c) and §2.15(3) (printed
p. 449). The statement module explains this provenance.

## Proof

The proof is a single application of the conditional theorem
`Langlands.productLeviCuspidalJacquetMultiplicity_of_upstream` from the published module
`Classification/ProductLeviCuspidalJacquetAssembly`. That theorem derives the target
from three Library statements, which it takes as hypotheses. The proof supplies the
published proofs of these statements:

* `Parabolic.refinedInductionTensor` (module `Parabolic/RefinedInductionTensorProof`)
  proves `Parabolic.RefinedInductionTensorTheorem`. Normalized refined induction of an
  external tensor product is the external tensor product of the blockwise normalized
  inductions.
* `CuspidalSupport.associatedJacquetFiltration F T n` (module
  `CuspidalSupport/AssociatedProof`) proves `AssociatedJacquetFiltrationTheorem F T n`.
  This is the general-linear geometric-lemma filtration of the upper Jacquet module of a
  quasicuspidal induction. The assembly needs it only for `0 < n`. The published theorem
  holds for every `n`, so the positivity hypothesis is ignored.
* `glOppositeCuspidalJacquetFiltrationFromUpper` (module
  `Classification/OppositeCuspidalJacquetFiltrationProof`) proves
  `GLOppositeCuspidalJacquetFiltrationFromUpperStatement`. It turns the upper
  filtration into the matching filtration of the general-linear opposite Jacquet module.

The assembly module itself proves the statement from these hypotheses as follows; its
Markdown gives the details.

1. `σ` is an external tensor product of irreducible Levi-cuspidal factors on the blocks
   of `B`. This uses the published cuspidal factorization
   `CuspidalSupport.padicLeviCuspidalFactorization`, the regrouping
   `FiniteTensor.flattenedTensorRegroupEquiv`, and `CuspidalSupport.glCuspidalTensor`.
   Factorization is proved here, not assumed.
2. The refined induction tensor theorem identifies the induced representation with the
   tensor product of the blockwise general-linear inductions. The published comparison
   `RefinedOppositeJacquetTensor.oppositeJacquetEquiv` identifies the refined opposite
   Jacquet module of that tensor product with the tensor product of the blockwise
   opposite Jacquet modules.
3. The blockwise general-linear opposite filtrations come from the opposite transfer
   applied to the associated Jacquet filtration. The finite external tensor product of
   these filtrations (`FiniteTensorFiltration.exists_external`) filters the refined
   opposite Jacquet module.
4. The graded pieces are indexed by families of minimal self-conjugating permutations of
   the blocks. `ProductLeviMinimalIndex.assembleEquiv` puts these families in bijection
   with the minimal self-conjugating permutations of `C` in `blockWeyl B`, using
   `blockPermOf`. `ProductLeviCuspidalJacquetAssembly.gradedEquiv` identifies each graded
   piece with the transport `CuspidalSupport.transport C C w σ`, moved along the inverse
   of `flattenedLeviEquiv`.
5. The counting theorem `finiteFamilyFiltrationMultiplicity` gives the length and the
   multiplicities. The associating permutations of `σ` and `τ` in `blockWeyl B` are
   exactly the indices whose graded piece is equivalent to `τ`.

All comparisons are actual `Representation.Equiv`s. The proof adds no hypotheses and uses
only the axioms `propext`, `Classical.choice` and `Quot.sound`.
