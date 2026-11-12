# Spectral presentations of supplied cuspidal contragredients: proof

Module: `Langlands.Automorphic.CuspidalDualPresentationExistenceProof`.
Author: Worker 5016. The finite-slice step is the published theorem of Task 5152
([CuspidalAdmissible/Existence](CuspidalAdmissible/Existence.md)); the presentation and universe
steps are the published constructions also used by
[CuspidalContragredientPresentationExistenceProof](CuspidalContragredientPresentationExistenceProof.md).

`Langlands.Automorphic.cuspidalDualPresentationExistence` proves the published proposition
`Langlands.Automorphic.CuspidalDualPresentationExistenceStatement.{uF, uP, uQ}` of
[CuspidalDualPresentationExistenceStatement](CuspidalDualPresentationExistenceStatement.md), for
all three independent universes `uF`, `uP`, `uQ`.

## Statement proved

For every number field `F : Type uF` with `[CompactSpace (AdeleQuotient F)]`, every `r : ℕ`, all
`T T' : CuspidalOperatorRealization F r` with `T'.realization.IsContragredientOf T.realization`,
and every input presentation `CuspidalSpectralPresentation.{uF, uP} T`, there is a presentation
`CuspidalSpectralPresentation.{uF, uQ} T'`. The hypotheses are exactly the published ones; no
unitary central character is assumed. The contragredient hypothesis and the input presentation
are not used: the proof works for every cuspidal operator realization `T'`.

## The implemented proof

1. `Langlands.Automorphic.cuspidalIrreducibleAdmissibleFiniteSliceExistence` (published proof of
   `CuspidalIrreducibleAdmissibleFiniteSliceExistenceStatement.{uF}`) applied to `T'` gives a
   nonzero actual finite slice `A` of `T'` whose finite adelic action is irreducible and
   admissible.
2. `CuspidalOperatorRealization.exists_presentation_of_finiteSlice`
   ([CuspidalSlicePresentation](CuspidalSlicePresentation.md)) applies Flath's theorem to `A` and
   assembles a presentation `P : CuspidalSpectralPresentation.{uF, uF} T'` with irreducible
   admissible local components at every finite place.
3. `CuspidalSpectralPresentation.exists_small`
   ([CuspidalPresentationUniverse](CuspidalPresentationUniverse.md)) transports `P` to a
   presentation whose factor carriers lie in the prescribed universe `uQ`.

The proof composes these three results.

## Relation to the target Markdown

The target Markdown records the statement as a derived proposition, the nonunitary analogue of
`CuspidalContragredientPresentationExistenceStatement`. The implemented route is that of the
unitary proof with its first step replaced: instead of the unitary countable-dual slice
(`exists_irreducibleAdmissible_finiteSlice_of_contragredient`), it uses the unconditional
irreducible admissible finite slice of an arbitrary cuspidal operator realization (the
finite-adelic part of Harish-Chandra's finiteness theorem for cusp forms, as cited and proved in
[CuspidalAdmissible/Existence](CuspidalAdmissible/Existence.md)). Step 2 is Flath's theorem
(Getz–Hahn 2024, Theorem 5.7.1), as cited in [CuspidalSlicePresentation](CuspidalSlicePresentation.md).
No admissibility, factorization or duality assumption is added.
