# Square gluing for the actual relative Picard pseudofunctor

This internal module connects the abstract square-gluing conditions of
`Langlands.CategoryTheory.PseudofunctorSquareGluing` with the published actual
Picard comparison functors. It deduces both conditions for affine squares of
ring pullbacks over a flat base from the published flat-base gluing theorem.
All declarations are in the namespace
`Langlands.AlgebraicGeometry.Picard.PicardGroupoid`.

## Overlap isomorphisms

- the imported `modHom_mapComp'_hom` and `realization_modHom_mapComp'_inv` give
  the underlying module maps of the composition comparisons of the line-bundle
  pseudofunctor `pseudofunctor`. Write `mod M` for the module underlying `M`,
  and `compIso g u u' h` for `UnitCocycleDescentUniqueness.compIso g u u' h
  (mod M)`, which goes from the iterated pullback `g^* (u^* (mod M))` to the
  composite pullback `u'^* (mod M)`. The forward comparison
  `(pseudofunctor.mapComp' u g u' hp).hom`, from the composite pullback to the
  iterated one, has underlying module map `(compIso g u u' h).inv`. This is the
  published `PicardGroupoid.modHom_mapComp'_hom`. The inverse comparison
  `(pseudofunctor.mapComp' u g u' hp).inv` has underlying module map
  `(compIso g u u' h).hom`. This follows from the first statement, because
  `moduleRealization.modHom` preserves composition and identities.
- `squareIso_pseudofunctor`: for a commuting square `w : i₁ ≫ j₁ = i₂ ≫ j₂` of
  schemes and an actual line bundle `Z` on the total corner,
  `squareIso pseudofunctor w Z = (squarePullbackIso i₁ i₂ j₁ j₂ w).app Z`.
  The right side is the published overlap isomorphism used by
  `squareGluingComparison`. The proof compares underlying module maps
  (`moduleRealization.hom_ext`). The left side is a forward comparison followed
  by an inverse one. The published `SquareGluingFullyFaithful.squarePullbackIso_app`
  and `UnitCocycleDescentUniqueness.squarePullbackIso_hom_eq_compIso` give the
  right side in the same form. This lemma is checked with a raised heartbeat
  limit, because comparing the two forms of the pulled-back objects is
  expensive for the kernel.
- `squareIso_relative`: for `f : X ⟶ S` and a commuting square
  `w : i₁ ≫ j₁ = i₂ ≫ j₂` in `Over S`, `squareIso (relative f) w Z` is the
  published `squarePullbackIso` of the base-changed square. The proof combines
  `squareIso_comp`, since `relative f` is `pseudofunctor` precomposed with
  `relativeSpace f`, with `squareIso_pseudofunctor`.

## Gluing from the comparison functor

For a commuting square `w` in `Over S`, let `C` be the published comparison
functor `relativeSquareComparison f i₁ i₂ j₁ j₂ w`.

- `isSquareHomGluing_of_isEquivalence`: if `C` is an equivalence, then
  `IsSquareHomGluing (relative f) w` holds. By `squareIso_relative`, a
  compatible pair `(φ₁, φ₂)` is a morphism of gluing data. Fullness gives the
  glued morphism, and faithfulness gives its uniqueness.
- `isSquareEffective_of_isEquivalence`: if `C` is an equivalence, then
  `IsSquareEffective (relative f) w` holds. The datum `(M₁, M₂, e)` is an
  object of `SquareGluingData`. The chosen preimage under `C`, with the
  components of `objObjPreimageIso`, gives the glued bundle and both
  isomorphisms. The commutation of that isomorphism of gluing data is the
  required compatibility, by `squareIso_relative`.

## Affine squares over a flat base

Let `k` be a commutative ring and `g : Y ⟶ Spec k` a flat morphism. Let
`R = A ×_C B` be a pullback of commutative `k`-algebras with maps `p`, `q`,
`a`, `b` (hypothesis `h`), with `b : B → C` surjective with nilpotent kernel.

- `affine_isSquareEffective` and `affine_isSquareHomGluing`: both gluing
  conditions hold for `relative g` on the affine square
  `affineSquare_comm p q a b h` of affine bases. They follow from the
  published `FlatInfinitesimalGluing.affineSquareComparison_isEquivalence`,
  because `affineSquareComparison` is by definition the comparison functor of
  that square.

## Provenance

Internal. These are translations between the abstract square conditions and
the published actual Picard gluing theorems. No literature statement is
transcribed. They supply conditions (S1) and (S2) in the form used by
`exists_lift_of_square_gluing`.
