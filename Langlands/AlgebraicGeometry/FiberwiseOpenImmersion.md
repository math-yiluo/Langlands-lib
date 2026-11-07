# The fibrewise criterion for open immersions

This module proves `Langlands.AlgebraicGeometry.isOpenImmersion_of_fiberwise`.
Let S be a scheme and let X, Y be objects of `Over S`. Let f : X → Y be a
morphism over S. Assume:

- X → S is flat and locally of finite presentation;
- Y → S is locally of finite type;
- for every point s of S, the base change of f along
  `S.fromSpecResidueField s : Spec κ(s) → S` is an open immersion.

Then the underlying scheme morphism `f.left` is an open immersion. The fibre
at s is written in the form used by the published fibrewise flatness theorem,
`((Over.pullback (S.fromSpecResidueField s)).map f).left`.

## Provenance

This is an internal helper lemma, written for the local-ring Isomorphism
Theorem task. Its role there is to show that the big-cell multiplication map
over a local ring is an open immersion, given that it is one over every
residue field of the base. The proof assembles two published results:

- `Langlands.AlgebraicGeometry.fiberwiseFlatness`, the finite-presentation
  fibrewise flatness criterion. It covers the first assertion of Stacks
  Lemma 37.16.4, tag [039E](https://stacks.math.columbia.edu/tag/039E).
- Mathlib's `AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono`: a flat
  monomorphism that is locally of finite presentation is an open immersion.
  This is (3) ⇒ (1) of Stacks Theorem 41.14.1, tag
  [025G](https://stacks.math.columbia.edu/tag/025G).

The route goes through the diagonal of f. It uses neither differentials nor
the étale-local structure of unramified morphisms.

## Auxiliary lemmas

The namespace `Langlands.AlgebraicGeometry.FiberwiseOpenImmersion` contains
three lemmas. In each, f : X → Y is a morphism in `Over S`, Δ is
`pullback.diagonal f : X → X ×_Y X` (the fibre product taken in `Over S`), and
σ_s is `S.fromSpecResidueField s`.

- `pullback_map_diagonal`: pulling Δ back along σ_s and composing with
  `pullbackComparison` gives the diagonal of the pulled-back morphism. Both
  sides are maps into a fibre product. The proof compares the two projections
  (`pullback.hom_ext`) and simplifies.
- `isIso_pullback_map_diagonal`: if the fibre of f at s is a monomorphism of
  schemes, then the pullback of Δ along σ_s is an isomorphism in
  `Over (Spec κ(s))`. A morphism in an over category is a monomorphism when its
  underlying morphism is (`Over.mono_of_mono_left`). The diagonal of a
  monomorphism is an isomorphism (`pullback.isIso_diagonal_iff`). The
  comparison map `pullbackComparison` is an isomorphism because
  `Over.pullback` preserves limits, being a right adjoint. The previous lemma
  then writes the pulled-back Δ as an isomorphism composed with an inverse.
- `locallyOfFinitePresentation_pullback_hom`: X ×_Y X is locally of finite
  presentation over S. First, f.left is locally of finite presentation: its
  composite with Y → S is X → S, and Y → S is locally of finite type
  (`locallyOfFinitePresentation_of_comp`, imported from
  `Langlands.AbelianScheme.TorsionFiniteEtale`). The forgetful functor
  `Over.forget S` sends the pullback square of f along f to a pullback square
  of schemes. So the first projection X ×_Y X → X is a base change of f.left
  and is locally of finite presentation. Composing with X → S proves the claim.

## Proof of the theorem

1. As above, f.left is locally of finite presentation. Every fibre of f is an
   open immersion, so it is flat. `fiberwiseFlatness` therefore makes f.left
   flat.
2. Each fibre of f is an open immersion and hence a monomorphism. By
   `isIso_pullback_map_diagonal`, every residue-field fibre of Δ is an
   isomorphism. Its underlying scheme morphism is one too, since the
   forgetful functor `Over.forget` maps isomorphisms to isomorphisms.
3. Apply `fiberwiseFlatness` to Δ : X → X ×_Y X over S. Here X → S is flat
   and locally of finite presentation by hypothesis. The target is locally of
   finite presentation, hence of finite type, over S by
   `locallyOfFinitePresentation_pullback_hom`. Every fibre of Δ is an
   isomorphism, hence flat. So Δ.left is flat.
4. Δ.left is locally of finite presentation by the same composition argument
   (`Over.w Δ` identifies its composite with the structure map of X ×_Y X with
   X → S). It is a monomorphism, since composing it with the first projection
   gives the identity of X. `IsOpenImmersion.of_flat_of_mono` now makes Δ.left
   an open immersion.
5. Δ.left is surjective. Let w be a point of X ×_Y X lying over s ∈ S. By
   `Scheme.Pullback.exists_preimage_pullback`, applied with the closed point
   of Spec κ(s), w lifts to a point w' of the fibre of X ×_Y X over s. By
   step 2 the fibre of Δ at s is an isomorphism, so w' = Δ_s(x') for some x'.
   The base-change square of Δ commutes: first projection then Δ.left equals
   Δ_s then first projection. This is the identity `pullback.lift_fst`, since
   `Over.pullback_map_left` describes the pulled-back map as a
   `pullback.lift`. Hence Δ.left maps the image of x' in X to w.
6. A surjective open immersion is an isomorphism
   (`isIso_iff_isOpenImmersion_and_surjective`). So Δ.left is an isomorphism.
   `Over.forget S` reflects isomorphisms, so Δ is an isomorphism in `Over S`.
   By `pullback.isIso_diagonal_iff`, f is a monomorphism in `Over S`, and
   hence f.left is a monomorphism of schemes.
7. f.left is flat (step 1), locally of finite presentation, and a
   monomorphism. `IsOpenImmersion.of_flat_of_mono` concludes that f.left is an
   open immersion.

The theorem uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.
