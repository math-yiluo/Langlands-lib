# Closed loci of liftings and of equalities over a field

Author: Worker 1412.

This module is an internal helper for the proof of
`Langlands.GroupScheme.AutomorphicAction.AffineFiniteTypeCocycleModelStatement`
(see [AffineFiniteTypeCocycleModelProof](../GroupScheme/AutomorphicAction/AffineFiniteTypeCocycleModelProof.md)).
It specializes the Library theorem
`Langlands.AlgebraicGeometry.ClosedFactorizationLocusProof.closedFactorizationLocus`
(see [ClosedFactorizationLocusStatement](ClosedFactorizationLocusStatement.md), whose
statement is extracted from Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd
edition, A.8.10(1)) to an affine scheme `X` over a field. It rephrases that theorem
in two forms used by the proof. No new literature claim is formalized.

Both theorems are in `Langlands.AlgebraicGeometry.ClosedLiftingLocus`. They hold for a
field `k : Type u` and objects of `Over (Spec (CommRingCat.of k))`. Here `X ⊗ Y` is the
fibre product over `Spec k` and `X ◁ t : X ⊗ T ⟶ X ⊗ Y` is `𝟙 X × t`. In each
theorem the witnesses `Z` and `i` are chosen once and work for every test scheme
`T` over `Spec k` and every `t : T ⟶ Y`; no hypothesis is placed on `T`.

- `exists_lifting_locus X Y A B j hj Ψ`: let `X` have affine structure morphism, let
  `j : A ⟶ B` have a closed immersion `j.left`, and let `Ψ : X ⊗ Y ⟶ B`. Then there are
  `Z` and `i : Z ⟶ Y` with `i.left` a closed immersion such that, for all `T` and
  `t : T ⟶ Y`, `t` factors through `i` if and only if there is
  `σ : X ⊗ T ⟶ A` with `σ ≫ j = (X ◁ t) ≫ Ψ`. In words: the locus of `t` over which
  `Ψ` restricted to `X × T` lifts through `j` is closed.
- `exists_equalizer_locus X Y G f₁ f₂`: let `X` have affine structure morphism, let
  `G.hom` be separated, and let `f₁ f₂ : X ⊗ Y ⟶ G`. Then there are `Z` and `i : Z ⟶ Y`
  with `i.left` a closed immersion such that, for all `T` and `t : T ⟶ Y`, `t`
  factors through `i` if and only if `(X ◁ t) ≫ f₁ = (X ◁ t) ≫ f₂`.

## Proofs

Both proofs apply `closedFactorizationLocus` over `R = CommRingCat.of k`. Its
hypotheses on `X` hold over a field. `X.hom` is affine by assumption and flat because
the base is a field. The coordinate-projectivity hypothesis
`HasFpqcProjectiveCoordinateModule X` is witnessed by `B = k`: `k` is faithfully flat
over itself, and every module over a field is projective.

For `exists_lifting_locus`, take `D` to be the pullback of `j` and `Ψ` in
`Over (Spec k)`, with `d = pullback.snd j Ψ : D ⟶ X ⊗ Y`. Then `d.left` is a closed
immersion, because closed immersions are stable under pullback and the forgetful
functor to schemes carries this pullback square to a pullback square. A
factorization `q ≫ d = X ◁ t` gives the lift `σ = q ≫ pullback.fst j Ψ` by the
pullback condition. Conversely, a lift `σ` gives `q = pullback.lift σ (X ◁ t) _`.

For `exists_equalizer_locus`, take `D` to be the equalizer of `f₁` and `f₂` with its
inclusion `equalizer.ι f₁ f₂`. Its underlying morphism is a closed immersion because
`G.hom` is separated (Mathlib's instance for equalizers into separated schemes). A
factorization through the equalizer exists exactly when the two composites agree
(`equalizer.condition`, `equalizer.lift`).
