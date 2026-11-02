# Open images of flat morphisms locally of finite presentation

Module `Langlands.AlgebraicGeometry.Descent.LocallyQuasiFiniteDescent.FlatImage`, namespace
`Langlands.AlgebraicGeometry.LocallyQuasiFiniteDescent`. This is a helper for the proof of
`Langlands.AlgebraicGeometry.FppfSeparatedLocallyQuasiFiniteDescentStatement` (Stacks Tag 02W8 in
sheaf form). It is internal: Stacks has no tag for it. It is the sheaf-form version of the
remark in the Stacks proof of 02W8 that the image of an open of `V` under the descent
isomorphism is open, because fppf morphisms are universally open. In the Lean proof it is used to
show that open charts of the descended sheaf are representable open subfunctors.

## Definitions

- `flatLFPScheme : MorphismProperty Scheme` is `Flat ⊓ LocallyOfFinitePresentation`. It has
  instances for stability under base change and under composition.
- `flatLFP S : MorphismProperty (Over S)` is the inverse image of `flatLFPScheme` under
  `Over.forget S`. It has instances for stability under base change and composition and for
  respecting isomorphisms.
- For `p : R ⟶ T` in `Over S` with `p.left` flat and locally of finite presentation:
  - `flatImageOpen p : T.left.Opens` is the set-theoretic image `Set.range p.left`. It is
    open because such morphisms are open maps (`Scheme.Hom.isOpenMap`).
  - `flatImage p : Over S` is this open subscheme, over `S` via `T`.
  - `flatImageι p : flatImage p ⟶ T` is its inclusion.
  - `toFlatImage p : R ⟶ flatImage p` is the factorization of `p` through its open image.

## Statements

- `flatLFP_relative_map`: if `f.left` is flat and locally of finite presentation, then
  `schemeYoneda S` applied to `f` is `flatLFP S` relative to schemes.
- `flatImageι_isOpenImmersion`, `range_flatImageι`, `toFlatImage_fac`: the inclusion is an
  open immersion with image `Set.range p.left`, and `toFlatImage p ≫ flatImageι p = p`.
- `toFlatImage_flat`, `toFlatImage_locallyOfFinitePresentation`, `toFlatImage_surjective`: the
  factorization is flat, locally of finite presentation and surjective.
- `sheafify_range_schemeYoneda_map_of_flat`: the fppf sheafification of the image subfunctor of
  `h p` equals the image subfunctor of `h (flatImageι p)`, where `h = schemeYoneda S`.
- `preimage_sheafify_range_eq`: let `a : G ⟶ F` and `g : h T ⟶ F` be maps of presheaves.
  Suppose `k : h P ⟶ G` and `h p` form a pullback square of `a` along `g`, with `p` flat and
  locally of finite presentation. Then the preimage under `g` of the sheafified image of `a` is
  the image subfunctor of `h (flatImageι p)`.
- `toSheafifyRange g p sq` is the induced map from `h (flatImage p)` to the sheafified image
  of `a`. It satisfies `toSheafifyRange_ι`. `isPullback_toSheafifyRange` says the base change of
  the sheafified image of `a` along `g` is `h (flatImage p)`.
- `sheafify_range_open_of_flat`: if `a : G ⟶ F` is `flatLFP S` relative to schemes, then the
  inclusion of the fppf sheafified image of `a` into `F` is an open immersion of presheaves
  (`AlgebraicSpace.IsOpenImmersion`).

## Proof

The factorization through the open image comes from the Library lemma
`OpenSubfunctorLifting.factors_through_open_iff`. Its flatness and local finite presentation
come from cancelling the monomorphism `flatImageι p`
(`IsStableUnderBaseChange.hasOfPostcompProperty_monomorphisms`). Surjectivity holds by
construction. `toFlatImage p` is an fppf covering, so `h (toFlatImage p)` is locally surjective
(`isLocallySurjective_schemeYoneda_map`). The Library lemma `sheafify_range_comp` then
identifies the sheafified image of `h p` with the open chart `h (flatImageι p)`. The preimage
statement combines this with `sheafify_preimage` (sheafification commutes with preimages) and
`OpenSubfunctorLifting.range_eq_preimage_of_isPullback`. The pullback square comes from
`OpenSubfunctorLifting.isPullback_subfunctor_of_range`. For `sheafify_range_open_of_flat`,
every base change of `a` along a test map `g` is represented by some `p` that is flat and
locally of finite presentation. The pullback square above exhibits the corresponding base
change of the sheafified image as the open subscheme `flatImage p`
(`MorphismProperty.relative.of_exists`).
