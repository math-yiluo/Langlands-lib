# Kernels of a represented base change

Module `Langlands.AlgebraicGeometry.Descent.LocallyQuasiFiniteDescent.Transport`, namespace
`Langlands.AlgebraicGeometry.LocallyQuasiFiniteDescent`. This is a helper for the proof of
`Langlands.AlgebraicGeometry.FppfSeparatedLocallyQuasiFiniteDescentStatement` (Stacks Tag 02W8 in
sheaf form). It is internal: Stacks has no tag for it. In the descent argument it plays the role
of the canonical descent datum on the base change `W`. Here that datum is written as an explicit
morphism `W ×_T V ⟶ W` and not through a descent-data formalism.

## Setting

`S` is a scheme and `h` is `schemeYoneda S`. `F` is a presheaf on `Over S` and
`p : F ⟶ h T`. The map `g : V ⟶ T` is in `Over S`. `c : h W ⟶ F` and `w : W ⟶ V` form a
pullback square `hpb : IsPullback c (h w) p (h g)`. So `W` represents the base change of `F`
along `g`. Pullbacks below are taken in `Over S`.

## Statements

- `app_eq_app_iff`: for `a b : Z ⟶ W`, the points `c(a)` and `c(b)` of `F(Z)` are equal iff
  `h a ≫ c = h b ≫ c`.
- `eq_of_isPullback`: two points of `W` with the same image in `F` and in `V` are equal.
- `comp_eq_of_comp_eq`: two points of `W` with the same image in `F` have the same image in
  `T`, i.e. `a ≫ w ≫ g = b ≫ w ≫ g`.
- `firstLift w g : (W ×_T V) ×_T V ⟶ W ×_T V` is `(π₁ ∘ π₁, π₂)`, with `firstLift_fst` and
  `firstLift_snd`.
- `secondMap hpb : W ×_T V ⟶ W` is the map whose image in `F` is that of the first projection
  (`secondMap_c`) and whose image in `V` is the second projection (`secondMap_w`). It is
  obtained from the pullback property of `hpb` and full faithfulness of `h`.
- `exists_lift_of_comp_eq`: if `a` and `b` have the same image in `F`, there is
  `κ : Z ⟶ W ×_T V` with `κ ≫ π₁ = a` and `κ ≫ secondMap hpb = b`.
- `diag_secondMap`: the diagonal `(𝟙, w) : W ⟶ W ×_T V` is a section of `secondMap hpb`.
- `secondLift hpb : (W ×_T V) ×_T V ⟶ W ×_T V` is `(secondMap ∘ π₁, π₂)`, with
  `secondLift_fst` and `secondLift_snd`.
- `firstLift_secondMap`: the cocycle identity
  `firstLift ≫ secondMap = secondLift ≫ secondMap`.
- `app_eq_app_iff_comp_eq` (kernel comparison). Let `q : W ⟶ Y` and `y : Y ⟶ T` satisfy
  `q ≫ y = w ≫ g`. Suppose `π₁ ≫ q = secondMap hpb ≫ q` on `W ×_T V`, and suppose `q` and `w`
  are jointly monic. Then for all `a b : Z ⟶ W`, `c(a) = c(b)` iff `a ≫ q = b ≫ q`.

## Proof

All statements follow from the universal property of the pullback square `hpb` and from full
faithfulness of `h` (`Functor.map_injective`, `Functor.preimage`). `app_eq_app_iff` uses
`uliftYonedaEquiv_comp` and injectivity of `uliftYonedaEquiv`. The identities for `secondMap`
are checked by `eq_of_isPullback`, comparing images in `F` and in `V` separately.

For the kernel comparison: if `c(a) = c(b)`, factor `(a, b)` as `κ` by
`exists_lift_of_comp_eq` and use `π₁ ≫ q = secondMap ≫ q`. Conversely, if `a ≫ q = b ≫ q`,
then `a` and `b ≫ w` agree in `T` because `q ≫ y = w ≫ g`. So `κ = (a, b ≫ w)` is a point of
`W ×_T V`. Joint monicity of `q` and `w` gives `κ ≫ secondMap = b`, and then
`c(b) = c(κ ≫ π₁) = c(a)` by `secondMap_c`.
