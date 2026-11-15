# Irreducibility of u(δ,k+1) × u(δ,k−1) for Speh representations

This module proves the published proposition
`Langlands.Classification.SpehNeighborProductIrreducibility.{uF, uV} F T`
(module `Classification.SpehUnitarizabilityReductionStatement`) without
hypotheses. The theorem is
`Langlands.Classification.spehNeighborProductIrreducibility`. It holds for
every prime `p`, every `F : PadicField.{uF} p`, every `T : F.TopologicalData`,
and independent universes `uF` and `uV`.

This is Badulescu (2014), Theorem 1(b)(ii). Let δ be a discrete series and
k ≥ 2, and let `Sup` and `Sdown` be actual smooth representations (carrier
universe `max uF uV`) that are the Speh representations u(δ,k+1) and
u(δ,k−1) of the datum. Then their normalized product
`(T.binaryPositiveProductFunctor _ _).obj (Sup, Sdown)` is irreducible.

## Proof

The module contains two theorems.

`spehNeighborProductIrreducibility_of_universalAubertCorrectness` takes the
published proposition `MoeglinWaldspurger.UniversalAubertCorrectness` at
universes `uF` and `max uF uV` as a hypothesis `hMW` and proves the target.
It composes three results.

1. `Langlands.Aubert.headProductLeadingTerm` (published, module
   `Aubert.HeadProductLeadingTermProof`) proves the head-product
   leading-term statement `HeadProductLeadingTermStatement.{uF, uV} F T`.
2. `neighborRectangleConstituentLengthBound_of_aubertCorrectness`
   (`SpehNeighborRectangleLengthBound`) turns MW Aubert correctness for this
   `p`, `F` and `T`, together with the head-product statement, into the
   rectangle constituent length bound
   `NeighborRectangleConstituentLengthBound`. The hypothesis is applied as
   `hMW p F T`. Its carrier universe `max uF uV` is the one that lemma uses.
3. `spehNeighborProductIrreducibility_of_rectangle_bound`
   (`SpehNeighborRectangleReduction`) derives the target from the
   head-product statement and the bound.

`spehNeighborProductIrreducibility` then applies this theorem to the
published theorem `Langlands.MoeglinWaldspurger.universalAubertCorrectness`
(module `Classification.MoeglinWaldspurgerAubertCorrectnessProof`),
instantiated at universes `uF` and `max uF uV`. This removes the hypothesis,
so the result has exactly the type of the published statement.

## Provenance

This is a derived assembly from the imported modules. It adds no
mathematical content of its own. The statement proved is Badulescu,
*On p-adic Speh representations* (2014), Theorem 1(b)(ii).
