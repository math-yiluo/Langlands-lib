# Affine-valued maps on a proper integral scheme minus a factorial point

Module `Langlands.AlgebraicGeometry.HartogsAffineConstancy`. This is an internal supporting
module for the proof of `Langlands.GroupScheme.RankOneCentralCoverStatement` (the rank-one central
cover, `rankOneCentralCover` in `Langlands.GroupScheme.Reductive.RankOneCentralCoverProof`). It
combines the Hartogs extension
`FactorialHartogsExtension.restrict_surjective_of_generization_chain` with the Library's
constancy of affine-valued maps on proper connected reduced schemes
(`ProperConnectedAffineConstancy`). It needs no literature source.

## Statements

- `restrict_injective {X} [IsIntegral X] {W : X.Opens} {y} (hy : y ∈ W)`: restriction of
  global functions from `X` to a nonempty open `W` is injective.
- `exists_eq_const` (main theorem):

  ```
  theorem exists_eq_const {X : Scheme.{u}} [IsIntegral X] {k : Type u} [Field k]
      [IsAlgClosed k] (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] {W : X.Opens}
      {z y₀ y₁ : X} (hW : ∀ y : X, y ∉ W ↔ y = z) (h₀₁ : y₀ ⤳ y₁) (h₁z : y₁ ⤳ z)
      (hne₀₁ : y₀ ≠ y₁) (hne₁z : y₁ ≠ z) [UniqueFactorizationMonoid (X.presheaf.stalk z)]
      {Y : Scheme.{u}} [IsAffine Y] (f : W.toScheme ⟶ Y) :
      ∃ c : Spec (CommRingCat.of k) ⟶ Y, f = W.ι ≫ p ≫ c
  ```

  Let `X` be proper and integral over an algebraically closed field. Let `W` be the
  complement of a point `z` whose stalk is factorial and which has a chain of two proper
  generizations. Then every morphism from `W` to an affine scheme factors through
  `Spec k`, so it is constant.

## The implemented proof

1. The global functions of `W` are those of `X`. The restriction `Γ(X, ⊤) → Γ(X, W)` is
   injective by `restrict_injective`, which compares images in the function field
   (`germ_injective_of_isIntegral`). It is surjective by the Hartogs extension. Since
   `W.ι.appTop` is this restriction (`Scheme.Opens.ι_appTop`, `Scheme.Opens.ι_image_top`),
   it is an isomorphism.
2. `p.appTop` is an isomorphism by `isIso_appTop_of_proper_connected_reduced`, because an
   integral scheme is connected and reduced. Hence `(W.ι ≫ p).appTop` is an isomorphism.
3. `W` has a rational point. `X` is a Jacobson space
   (`LocallyOfFiniteType.jacobsonSpace`), so the nonempty open `W` contains a closed
   point `x` (`nonempty_inter_closedPoints`). Over the algebraically closed field `k`,
   `pointOfClosedPoint` gives a section of `p` through `x`. It lifts through the open
   immersion `W.ι`, giving `s` with `s ≫ W.ι ≫ p = 𝟙`.
4. `affineMap_eq_constant_of_isIso_appTop` gives `f = (W.ι ≫ p) ≫ s ≫ f`. So
   `c = s ≫ f` works.
