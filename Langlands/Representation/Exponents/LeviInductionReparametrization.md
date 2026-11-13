# Normalized induction does not depend on the parametrization of the Levi

Module `Langlands.Representation.Exponents.LeviInductionReparametrization`.

## Purpose and provenance

This is an internal transport lemma with no literature counterpart. The published
`leviInductionFunctor q lQ rQ …` induces representations of the source points of a Levi
map `lQ : L → Q`, through the point equivalence `leviPointsEquiv q lQ` onto
`pointImage (lQ ≫ q)`. When the same parabolic `Q` is given a second Levi map
`lQ' : M → Q` with the same image, the two inductions agree after pulling back along the
point equivalence `M(k) ≃ L(k)`. The proof of Renard VII.4.2 (ii) needs this to move a
standard Levi `M₂` onto the isomorphic standard Levi `M₁` of the other triplet.

## Declarations

- `Langlands.Aubert.General.normalizedInductionFunctor_obj_pullback_congr`. Let
  `L = L'` be two literally equal Levi subgroups of the same parabolic `P`, with
  decompositions `h`, `h'` and the same radical `N`. Let `φ : L ≃ K` and `φ' : L' ≃ K`
  be topological group equivalences that agree on `L = L'`, and let `σ` be a smooth
  representation of `K`. Then
  `(normalizedInductionFunctor h hN).obj (σ.pullback φ) =
   (normalizedInductionFunctor h' hN).obj (σ.pullback φ')`. Proof: substitute
  `L' := L`; then `φ' = φ` by extensionality, and both sides are literally equal.
- `RepresentedParabolic.leviInductionFunctor_obj_pullback_eq`. Let `lQ : L → Q` and
  `lQ' : M → Q` be rational Levi maps of the same parabolic `q : Q → G` with the same
  radical `rQ`. Let `φ : M(k) ≃ₜ* L(k)` satisfy
  `map (lQ ≫ q) (φ m) = map (lQ' ≫ q) m` for all `m`. Then for every `τ`,

  ```
  (leviInductionFunctor q lQ' rQ …).obj (SmoothRep.pullback φ τ)
    = (leviInductionFunctor q lQ rQ …).obj τ.
  ```

  Proof: the hypothesis on `φ` gives `pointImage (lQ' ≫ q) = pointImage (lQ ≫ q)`.
  Both sides unfold to normalized induction of pullbacks of `τ`, along
  `(leviPointsEquiv q lQ').symm.trans φ` and `(leviPointsEquiv q lQ).symm`. These agree
  on common points by the same hypothesis, and the previous lemma applies.
