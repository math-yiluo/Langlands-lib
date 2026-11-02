# Quasi-affine open charts of a locally quasi-finite base change

Module `Langlands.AlgebraicGeometry.Descent.LocallyQuasiFiniteDescent.QuasiAffineChart`, namespace
`Langlands.AlgebraicGeometry.LocallyQuasiFiniteDescent`. This is a helper for the proof of
`Langlands.AlgebraicGeometry.FppfSeparatedLocallyQuasiFiniteDescentStatement` (Stacks Tag 02W8 in
sheaf form). The Stacks proof of 02W8 (Lemma 37.57.1) starts from an affine open `W¹ ⊆ V`. It
enlarges `W¹` to the quasi-compact open `W` that is stable under the descent datum, notes that
`W` is quasi-affine over the base (More on Morphisms, Lemma 37.43.2), and descends it. The main
lemma here does the same in sheaf form: for an affine open `U` of the base change `X'`, it
produces a represented open subfunctor of the descended sheaf `G` that contains the image of
`U`. The lemma itself is internal; Stacks has no tag for it.

## Statements

- `isQuasiAffine_of_locallyQuasiFinite` (Zariski's main theorem, quasi-affine form). Let
  `f : X ⟶ Y` be separated, locally quasi-finite and locally of finite type, with `Y` affine
  and `X` quasi-compact. Then `X` is quasi-affine.
- `openOver X U : Over S` is an open `U` of `X.left`, as a scheme over `S`.
  `openOverι X U : openOver X U ⟶ X` is its inclusion. Both are abbreviations.
- `exists_openChart` (quasi-affine chart step). Notation: `h = schemeYoneda S`. The setting:
  - `G` is an fppf sheaf on `Over S` and `p : G ⟶ h T`;
  - `a' : h X' ⟶ G` and `x' : X' ⟶ V` form a pullback square of `p` along `h g`, with
    `g : V ⟶ T`;
  - `x'.left` is separated, locally quasi-finite and locally of finite type;
  - `g.left = g' ≫ ι` for an open immersion `ι : D ⟶ T.left` from an affine scheme `D`, with
    `V.left` affine and `g'` flat and locally of finite presentation;
  - `U` is an affine open of `X'.left`.

  Then there are `Y : Over S`, an open immersion of presheaves `b : h Y ⟶ G` and
  `z : openOver X' U ⟶ Y` such that `h z ≫ b` is the restriction of `a'` to `U`.

## Proof of `exists_openChart`

The first lemma is Mathlib's Zariski main theorem: `f.toNormalization` is an immersion, and
the normalization is affine over the affine scheme `Y`, so `X` is quasi-affine
(`Scheme.IsQuasiAffine.of_isImmersion`).

For the chart, let `u : U ⟶ X'` be the inclusion and `b₀ = h u ≫ a'`. `g` is flat and locally of
finite presentation, so its base change `a'` is `flatLFP S` relative to schemes (module
`FlatImage`). So is `b₀`. The base change of `b₀` along `a'` is represented by a map
`σ : U ×_T V ⟶ X'`. It is built from the pullback property of `a'` and full faithfulness of
`h`, and it lies in `flatLFP S`.

Let `Q` be the fppf sheafified image of `b₀`. By `sheafify_range_open_of_flat` its inclusion
into `G` is an open immersion, so `Q` is a sheaf (Library `isSheaf_of_open`). By
`isPullback_toSheafifyRange`, the base change of `Q` along `a'` is the open image `W ⊆ X'` of
`σ`, with `c₀ : h W ⟶ Q`. Pasting with the square for `a'` shows that `c₀` and `W ⟶ X' ⟶ V`
form a pullback square of `Q ⟶ G ⟶ h T` along `h g`.

The open `U` maps into `W`: the diagonal `U ⟶ U ×_T V` composed with `σ` is `u`, by
`eq_of_isPullback` from module `Transport`. Call the resulting map `j : U ⟶ W`. Then
`h j ≫ c₀` is the canonical locally surjective map from `h U` onto the sheafified image of
`b₀`, so `c₀` is locally surjective.

Next, `W` is quasi-affine. `U ×_T V` is affine, because it is affine over the affine scheme
`U` (base change of `g'` over `D`). `W` is its image under the surjection `toFlatImage σ`,
so `W` is quasi-compact. `W ⟶ V` is separated, locally quasi-finite and locally of finite type,
and `V` is affine. The first lemma applies.

`exists_iso_of_quasiAffine` (module `Core`) now gives `Y`, `q : W ⟶ Y` and `e : h Y ≅ Q` with
`h q ≫ e.hom = c₀`. Take `b = e.hom ≫ (Q ⟶ G)` and `z = j ≫ q`. `b` is an open immersion
because open immersions respect isomorphisms (`MorphismProperty.cancel_left_of_respectsIso`).
The required identity follows from `h q ≫ e.hom = c₀`, `c₀ ≫ (Q ⟶ G) = h (W ⟶ X') ≫ a'` and
`j ≫ (W ⟶ X') = u`.
