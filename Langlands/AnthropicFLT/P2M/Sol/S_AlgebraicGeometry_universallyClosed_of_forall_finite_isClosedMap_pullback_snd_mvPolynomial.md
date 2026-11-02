# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_universallyClosed_of_forall_finite_isClosedMap_pullback_snd_mvPolynomial`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_universallyClosed_of_forall_finite_isClosedMap_pullback_snd_mvPolynomial.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Proof (namespace `UCAffineGC4`).

- Elementary facts on closed maps of schemes: `coe_comp`, `isClosedMap_comp`, `isClosedMap_of_isIso`,
  `surjective_of_isIso`, `isClosedMap_of_iso_comp`, `isClosedMap_of_comp_closedImmersion`.
- `isClosedMap_of_surjective`: for a surjective `R`-algebra map `T' → T`, closedness of the base
  change to `Spec T'` implies closedness of the base change to `Spec T` (`Spec T ⟶ Spec T'` is a
  closed immersion, `IsClosedImmersion.spec_of_surjective`; `pullbackLeftPullbackSndIso`).
- `isClosedMap_of_algebra`: for every `R`-algebra `A` the base change to `Spec A` is closed. `A` is
  the directed union of the subalgebras `Algebra.adjoin R F` for finite sets `F`, each a quotient of
  a polynomial ring in finitely many variables; apply
  `AlgebraicGeometry.isClosedMap_pullback_snd_of_directed_subalgebra`.
- `isClosedMap_of_isAffine`: the same for an affine scheme `T` over `Spec R`, through
  `T ≅ Spec Γ(T, ⊤)`.
- `isClosedMap_pullback_snd`: for an arbitrary `T ⟶ Spec R`, closedness is checked on the
  preimages of the affine opens of `T` (`IsOpenCover.isClosedMap_iff_restrictPreimage`,
  `morphismRestrict`).
- `solution`: `universallyClosed_iff` and `MorphismProperty.universally_mk'` reduce to the
  closedness of the projection `pullback.fst t f`, which is `isClosedMap_pullback_snd` up to
  `pullbackSymmetry`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_universallyClosed_of_forall_finite_isClosedMap_pullback_snd_mvPolynomial.UCAffineGC4.coe_comp`
- theorem `P2MW.S_AlgebraicGeometry_universallyClosed_of_forall_finite_isClosedMap_pullback_snd_mvPolynomial.UCAffineGC4.isClosedMap_comp`
- theorem `P2MW.S_AlgebraicGeometry_universallyClosed_of_forall_finite_isClosedMap_pullback_snd_mvPolynomial.UCAffineGC4.isClosedMap_of_isIso`
- theorem `P2MW.S_AlgebraicGeometry_universallyClosed_of_forall_finite_isClosedMap_pullback_snd_mvPolynomial.UCAffineGC4.surjective_of_isIso`
- theorem `P2MW.S_AlgebraicGeometry_universallyClosed_of_forall_finite_isClosedMap_pullback_snd_mvPolynomial.UCAffineGC4.isClosedMap_of_iso_comp`
- theorem `P2MW.S_AlgebraicGeometry_universallyClosed_of_forall_finite_isClosedMap_pullback_snd_mvPolynomial.UCAffineGC4.isClosedMap_of_comp_closedImmersion`
- theorem `P2MW.S_AlgebraicGeometry_universallyClosed_of_forall_finite_isClosedMap_pullback_snd_mvPolynomial.UCAffineGC4.isClosedMap_of_surjective`
- theorem `P2MW.S_AlgebraicGeometry_universallyClosed_of_forall_finite_isClosedMap_pullback_snd_mvPolynomial.UCAffineGC4.isClosedMap_of_algebra`
- theorem `P2MW.S_AlgebraicGeometry_universallyClosed_of_forall_finite_isClosedMap_pullback_snd_mvPolynomial.UCAffineGC4.isClosedMap_of_isAffine`
- theorem `P2MW.S_AlgebraicGeometry_universallyClosed_of_forall_finite_isClosedMap_pullback_snd_mvPolynomial.UCAffineGC4.isClosedMap_pullback_snd`
- theorem `P2MW.S_AlgebraicGeometry_universallyClosed_of_forall_finite_isClosedMap_pullback_snd_mvPolynomial.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isClosedMap_pullback_snd_of_directed_subalgebra` (same contribution).
All modules also import `Mathlib`.
