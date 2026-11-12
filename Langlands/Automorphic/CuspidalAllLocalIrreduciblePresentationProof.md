# Cuspidal presentations irreducible and admissible at every finite place

Module: `Langlands.Automorphic.CuspidalAllLocalIrreduciblePresentationProof`.

This module proves the Library statement
`Langlands.Automorphic.CuspidalAllLocalIrreduciblePresentationExistenceStatement.{u, uQ}`
(module `Langlands.Automorphic.CuspidalAllLocalIrreduciblePresentation`), for arbitrary
universes `u` and `uQ`, with no added hypothesis.

## Main results

* `Langlands.Automorphic.cuspidalAllLocalIrreduciblePresentationExistence :
  CuspidalAllLocalIrreduciblePresentationExistenceStatement.{u, uQ}`.
  Let `F : Type u` be a number field with `[CompactSpace (AdeleQuotient F)]`, let `r : ℕ`, let
  `S : CuspidalOperatorRealization F r`, and let `_P : CuspidalSpectralPresentation.{u, uQ} S`
  be any spectral presentation. Then there is `Q : CuspidalSpectralPresentation.{u, u} S`
  such that for every finite place `v`, the actual embedded local component
  `Q.localComponent v` is irreducible and admissible. The conclusion holds at every finite
  place, including the exceptional sets of `Q`. The supplied `_P` is not used.
* `Langlands.Automorphic.cuspidalAllLocalIrreduciblePresentationExistence_of_finiteSlice`:
  the reduction. It takes a proof of the intermediate statement
  `CuspidalIrreducibleAdmissibleFiniteSliceExistenceStatement.{u}` (same module as the target)
  as an explicit argument and returns the target statement at `.{u, uQ}`. The final theorem
  applies it to the published proof of that intermediate statement, so the final theorem has
  no hypothesis.

## The implemented proof

1. **An irreducible admissible finite slice.** The published theorem
   `Langlands.Automorphic.cuspidalIrreducibleAdmissibleFiniteSliceExistence`
   (module `Langlands.Automorphic.CuspidalAdmissible.Existence`) proves
   `CuspidalIrreducibleAdmissibleFiniteSliceExistenceStatement.{u}`. Applied to `F`, `r` and
   `S`, it gives an actual finite slice `A : S.FiniteSlice` with `A.subspace.IsIrreducible`
   and `Langlands.IsAdmissible A.subspace.representation`. Its proof is the finite-adelic part
   of Harish-Chandra's finiteness theorem for cusp forms followed by a minimal-fixed-dimension
   argument. It assumes no unitary central character and no irreducibility of any component of
   a presentation.
2. **Flath assembly.** The published theorem
   `Langlands.Automorphic.CuspidalOperatorRealization.exists_presentation_of_finiteSlice`
   (module `Langlands.Automorphic.CuspidalSlicePresentation`) takes `S`, `A` and these two
   facts. It returns `Q : CuspidalSpectralPresentation.{u, u} S` with
   `∀ v, (Q.localComponent v).IsIrreducible ∧ (Q.localComponent v).IsAdmissible`. This is
   exactly the conclusion of the target. That theorem implements the route sketched in the
   target Markdown. It pulls the finite action of `A` back along
   `Langlands.Global.FiniteAdelicGL.restrictedProductEquiv`. It applies the Flath theorem
   `Langlands.flathRestrictedProductExistence` with local factors in universe `u`. It takes the
   Flath exceptional set as both exceptional sets of `Q` and sets
   `Q.unramified := FiniteTensorPresentation.unramifiedData`. Finally it transfers the local
   properties with `FiniteTensorPresentation.localComponent_isIrreducible_iff` and
   `localComponent_isAdmissible_iff`.

The reduction theorem consists of steps 1 and 2 with the intermediate statement as an
argument: it introduces `F`, the instances, `r`, `S` and `_P`, destructures the slice
supplied by the argument, and applies `exists_presentation_of_finiteSlice`.

## Public theorems used

* `Langlands.Automorphic.cuspidalIrreducibleAdmissibleFiniteSliceExistence`
  (`Langlands.Automorphic.CuspidalAdmissible.Existence`).
* `Langlands.Automorphic.CuspidalOperatorRealization.exists_presentation_of_finiteSlice`
  (`Langlands.Automorphic.CuspidalSlicePresentation`), which in turn uses
  `Langlands.flathRestrictedProductExistence`,
  `Langlands.Automorphic.FiniteTensorPresentation.unramifiedData`,
  `Langlands.Automorphic.FiniteTensorPresentation.localComponent_isIrreducible_iff` and
  `Langlands.Automorphic.FiniteTensorPresentation.localComponent_isAdmissible_iff`.

No local Langlands result, global functional equation or result that depends on the target
is used. The target pair and the pairs it imports are unchanged.

## Provenance

The mathematics is Flath's tensor product theorem applied to an irreducible admissible finite
slice of a cuspidal realization: Getz–Hahn, *An Introduction to Automorphic Representations*
(2024), Theorem 5.7.1, Lemma 6.3.6 and Theorem 6.3.7. The Lean proof here only combines the two
published theorems above.
