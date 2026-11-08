# Spectral presentations of supplied unitary cuspidal duals: proof

Module: `Langlands.Automorphic.CuspidalContragredientPresentationExistenceProof`.
Author: Worker 1827. The universe-transport step reuses the published construction of
Worker 1815 ([CuspidalPresentationUniverse](CuspidalPresentationUniverse.md)).

`Langlands.Automorphic.cuspidalContragredientPresentationExistence` proves the published
proposition `Langlands.Automorphic.CuspidalContragredientPresentationExistenceStatement.{uF, uP, uQ}`
of [CuspidalContragredientStatement](CuspidalContragredientStatement.md), for all three
independent universes `uF`, `uP`, `uQ` (in particular `uQ = 0` is allowed).

## Statement proved

For every number field `F : Type uF` with `[CompactSpace (AdeleQuotient F)]`, every `r : ℕ`, all
`T T' : CuspidalOperatorRealization F r` with `HasUnitaryCentralCharacter T` and
`T'.realization.IsContragredientOf T.realization`, and every input presentation
`_P : CuspidalSpectralPresentation.{uF, uP} T`, there is
`P' : CuspidalSpectralPresentation.{uF, uQ} T'` whose actual local components are irreducible
and admissible at every finite place. The hypotheses are exactly the published ones; the input
presentation `_P` is not used.

## The implemented proof

1. `CuspidalOperatorRealization.exists_irreducibleAdmissible_finiteSlice_of_contragredient`
   ([CuspidalContragredientSlice](CuspidalContragredientSlice.md)) gives a nonzero actual finite
   slice `A` of `T'` whose finite adelic action is irreducible and admissible. Its proof uses the
   Petersson-type band form of `T`, the countable dimension of the irreducible realization `T'`
   and the contragredient bijection, not Harish-Chandra finiteness.
2. `CuspidalOperatorRealization.exists_presentation_of_finiteSlice`
   ([CuspidalSlicePresentation](CuspidalSlicePresentation.md)) applies Flath's theorem to `A` and
   assembles a complete presentation `P : CuspidalSpectralPresentation.{uF, uF} T'`
   (the slice `A`, restricted tensor equivalence, reference vectors, normalized unramified data)
   with irreducible admissible local components at every finite place.
3. `CuspidalSpectralPresentation.exists_small` (published) replaces the local factors by
   equivalent irreducible factors with carriers in the prescribed universe `uQ`, transports
   admissibility, references and the tensor equivalence, rebuilds the unramified data, and keeps
   the all-place irreducibility and admissibility of the actual local components.

The proof is three lines composing these results.

## Relation to the target Markdown

The target Markdown sketches a derivation through cusp-form admissibility and finite/infinite
separation (Borel–Jacquet 1979 §§4.4–4.6; Getz–Hahn 2024 Theorem 6.3.4, Lemma 6.3.6) followed by
Flath's theorem (Getz–Hahn Theorem 5.7.1) and a comparison of spherical data through the input
presentation. The implemented route keeps the Flath step but replaces the admissibility input by
the unitary countable-dual argument of step 1. It obtains the normalized spherical data directly
from the irreducible admissible factors (`FiniteTensorPresentation.unramifiedData`), so no
comparison with the input presentation is needed. Its universe step is the published
small-realization transport. No admissibility, factorization, duality or pairing-surjectivity
assumption is added.
