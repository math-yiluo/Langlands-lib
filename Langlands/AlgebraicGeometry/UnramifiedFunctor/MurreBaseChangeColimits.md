# Base change of Murre's condition (F2)

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreBaseChangeColimits`
proves `BaseChange.filteredColimits`. If `F : (Over S)ᵒᵖ ⥤ Type v` satisfies
(F1a) `ZariskiSheaf F` and (F2) `FilteredColimits F`, then for every
`g : S' ⟶ S` the base change `baseChange g F` satisfies (F2). All names below
are in the namespace `Langlands.AlgebraicGeometry.UnramifiedFunctor.BaseChange`.

(F2) for the base change asks, for an open immersion `f : Spec A ⟶ S'`, that
`B ↦ F(Spec B ⟶ Spec A ⟶ S' ⟶ S)` preserve filtered colimits of `A`-algebras.
The composite `f ≫ g` is in general not an open immersion, so (F2) for `F` does
not apply directly. The proof shows that, given (F1a), the property holds for
every morphism `Spec R ⟶ S`.

## Abstract lemmas

- `exists_forall_of_finite`: in a filtered category, finitely many conditions
  on arrows out of `α` are satisfied by a single arrow `α ⟶ γ`. Each
  condition must be stable under postcomposition and satisfied by some arrow.
  The proof is induction over a `Finset`, using `IsFiltered.max` and
  `IsFiltered.coeq`.
- `isColimit_mapCocone_of_equalizer`: let `P, P_i, P_ij : C ⥤ Type w`, with
  `i, j` running over a finite type. Suppose there are natural maps
  `res i : P ⟶ P_i` and `a i j : P_i ⟶ P_ij`, `b i j : P_j ⟶ P_ij` with
  `a ∘ res i = b ∘ res j`, such that, objectwise, `P` is separated and glues
  along these maps. If every `P_i` and `P_ij` takes a cocone `c` over a
  filtered diagram to a colimit cocone, then so does `P`. The proof uses the
  characterization of filtered colimits of types
  (`Types.FilteredColimit.isColimitOf'`, `isColimit_eq_iff'`,
  `Types.jointly_surjective_of_isColimit`). For surjectivity, lift the finitely
  many restrictions of an element to a common stage. Equalize the finitely many
  compatibility conditions at a later stage, then glue. For injectivity,
  equalize the finitely many restrictions and use separation.
- `sep_glue_of_isSheafFor`: this lemma turns the sheaf condition for a family
  `π i : U i ⟶ X` into separation and gluing statements for an isomorphic
  family `ρ i = (e i).hom ≫ π i`. Compatibility is tested on chosen objects
  `W i j` with maps `p i j : W i j ⟶ V i` and `q i j : W i j ⟶ V j`. Every pair
  of arrows `Z ⟶ V i`, `Z ⟶ V j` that agree over `X` factors through them
  (`hlift`).

## Good morphisms

For `h : Spec R ⟶ S` let `specOver h : Under R ⥤ (Over S)ᵒᵖ` send
`B` to `Spec B ⟶ Spec R ⟶ S`. Call `h` good (`Good F h`) if
`specOver h ⋙ F` preserves filtered colimits (`PreservesFilteredColimitsOfSize.{u, u}`).

- `specOverCompIso φ h : specOver (Spec.map φ ≫ h) ≅ Under.map φ ⋙ specOver h`,
  and `preservesColimitsOfShape_underMap`: `Under.map φ` preserves filtered
  colimits. The forgetful functor `Under R ⥤ CommRingCat` reflects connected
  colimits, and the composite `Under.map φ ⋙ Under.forget R` is
  `Under.forget R'`, which preserves them.
  Together: `good_comp`, if `h` is good then so is `Spec.map φ ≫ h`.
- `algebraFunctorIso h`: on `CommAlgCat R`, `specOver h` is `algebraFunctor h`
  through `commAlgCatEquivUnder`. Hence `good_of_isOpenImmersion`: (F2) for
  `F` makes every open immersion `Spec R ⟶ S` good.

## Covers

Rings under `R` and their tensor products are pushouts in `CommRingCat`.

- `descL`, `descR`: the maps `A ⊗_R R_i → A ⊗_R (R_i ⊗_R R_j)` and
  `A ⊗_R R_j → A ⊗_R (R_i ⊗_R R_j)`, with `descL_w` and `descR_w` giving
  their compatibility with the structure maps.
- `exists_lift_pushout`: two morphisms `Z ⟶ Spec (A ⊗_R R_i)` and
  `Z ⟶ Spec (A ⊗_R R_j)` agreeing in `Spec A` factor through
  `Spec (A ⊗_R (R_i ⊗_R R_j))` via `Spec (descL)` and `Spec (descR)`. Spec takes
  pushouts to pullbacks (`isPullback_SpecMap_pushout`), so the factorization
  comes from two pullback lifts.
- `pieceT α = Under.pushout α ⋙ Under.map α` (`B ↦ B ⊗_R A` as a ring under
  `R`), with natural maps `resNat α : 𝟭 ⟶ pieceT α`, `natL`, `natR`, and
  `resNat_natL : resNat φ_i ≫ natL = resNat φ_j ≫ natR`.

## Locality of goodness and the theorem

- `preserves_piece`: if `Spec.map α ≫ h` is good, then
  `pieceT α ⋙ specOver h ⋙ F` preserves filtered colimits. `Under.pushout α`
  is a left adjoint (`Under.mapPushoutAdj`), and
  `Under.map α ⋙ specOver h ⋙ F ≅ specOver (Spec.map α ≫ h) ⋙ F`.
- `sep_glue`: suppose finitely many maps `φ i : R ⟶ R_i` have `Spec (φ i)` an
  open immersion and jointly cover `Spec R`. Then for every `B` under `R`,
  `B ↦ F(Spec B)` is separated and glues along `resNat`, `natL` and `natR`.
  The schemes `Spec (B ⊗_R R_i)` form an open cover of `Spec B`
  (`Scheme.Cover.mkOfCovers`). The maps are open immersions as base changes of
  `Spec (φ i)` (`MorphismProperty.of_isPullback`), and they cover by
  `Scheme.exists_preimage_of_isPullback`. Then (F1a) for this cover and
  `sep_glue_of_isSheafFor` apply, with `hlift` from `exists_lift_pushout`.
- `good_of_cover`: in that situation, if every `Spec (φ i) ≫ h` is good, so is
  `h`. This is `isColimit_mapCocone_of_equalizer` with
  `P_i = pieceT (φ i) ⋙ specOver h ⋙ F` and
  `P_ij = pieceT (φ i ≫ pushout.inl (φ i) (φ j)) ⋙ specOver h ⋙ F`.
  `preserves_piece` and `good_comp` give the hypotheses on the `P_i` and
  `P_ij`.
- `good_all`: with (F1a) and (F2), every `h : Spec R ⟶ S` is good. For
  `x ∈ Spec R`, `Scheme.exists_affine_mem_range_and_range_subset` gives an
  affine open immersion `f₁ : Spec R₁ ⟶ S` through `h x`. Applied again, it
  gives an affine open immersion `g_x : Spec R' ⟶ Spec R` through `x` with
  image inside `h⁻¹(range f₁)`. Then `g_x ≫ h` factors through `f₁`
  (`IsOpenImmersion.lift`). The factor is `Spec.map` of a ring map
  (`Spec.preimage`), so `g_x ≫ h` is good by `good_of_isOpenImmersion` and
  `good_comp`. Since `Spec R` is quasi-compact, finitely many of the `g_x`
  cover it (`isCompact_univ.elim_finite_subcover`). Writing `g_x = Spec.map _`
  and applying `good_of_cover` gives the claim.
- `algebraFunctorCompIso f g : algebraFunctor f ⋙ (Over.map g).op ≅ algebraFunctor (f ≫ g)`.
- `filteredColimits`: for an open immersion `f : Spec A ⟶ S'`, the morphism
  `f ≫ g` is good by `good_all`. The functor `algebraFunctor f ⋙ baseChange g F`
  is isomorphic to the composite of the equivalence
  `commAlgCatEquivUnder (CommRingCat.of A)` with `specOver (f ≫ g) ⋙ F`
  (`algebraFunctorIso`, `algebraFunctorCompIso`). An equivalence preserves
  colimits, so the composite preserves filtered colimits.
