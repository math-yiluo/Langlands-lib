# Line bundles that are locally trivial over the base

Authors: Worker 5705.

Helper module of the proof of `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemStatement` (entry module `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemProof`), written for Task 5705. It contains no `sorry` and no new axioms.

## Content

Namespace `Langlands.AlgebraicGeometry.Picard.PushforwardLineBundle`. Let `q : Z ⟶ T` be a
morphism such that `q.app U : Γ(T, U) → Γ(Z, q⁻¹U)` is bijective for every open `U`.

- `isFrameOn_pushforward`: a frame of `F` over `q⁻¹U` is a frame of the pushforward `q_* F` over
  `U`.
- `isLocallyFreeRankOne_pushforward`: if `F` has frames over the preimages of an open cover of
  `T`, then `q_* F` is a line bundle.
- `isIso_counit`, `nonempty_iso_pullback_pushforward`: the counit `q^* q_* F ⟶ F` is then an
  isomorphism (FLT `counit_app_pullbackLocalSection`, Library `isIso_of_bijective_of_basis`).
- `exists_classOf_pullback`: a Picard class on `Z` (Library `Picard.Group`) that is trivial over
  the preimages of an open cover of `T` is the pullback of the class of a line bundle on `T`.

## Source

Kleiman, *The Picard scheme* (arXiv math/0504020v1), Lemma 2.7 (p.18): if `𝒪_S ≅ f_*𝒪_X`, a locally
free sheaf `M` on `X` is a pullback from `S` when `f_*M` is locally free and `f^*f_*M → M` is an
isomorphism. This file proves the rank-one case needed here, in the form: a class trivial over the
preimages of an open cover of the base is pulled back. The hypothesis `𝒪_T ≅ q_*𝒪_Z` (on every
open) holds universally for proper flat morphisms with geometrically reduced and connected fibres
(Kleiman, Exercise 3.11, p.25); in the proof it is supplied by the FLT port's
`bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected`.
