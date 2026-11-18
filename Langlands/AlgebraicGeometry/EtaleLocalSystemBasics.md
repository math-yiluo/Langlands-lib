# Étale local systems: isotriviality and coefficient groups

This module adds basic facts to the published local-system definitions of
`Langlands.AlgebraicGeometry.EtaleLocalSystem`. It defines Conrad's notion of an
isotrivial sheaf, and shows that a finitely generated local system on a connected base
has a single coefficient group. All declarations are in the namespace
`Langlands.AlgebraicGeometry.EtaleLocalSystem`. The schemes are in universe `u` and the
coefficient groups in universe `v`. As in the imported module, the presheaves take values
in `AddCommGrpCat.{max u v}`.

## Definition

- `IsIsotrivial F`, for `F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{max u v}`, means that:
  - `F` is an étale sheaf (`IsEtaleSheaf F`, the published sheaf condition for the big
    étale topology on schemes over `S`);
  - there are a scheme `S'` and a morphism `p : S' ⟶ S` that is finite, étale and
    surjective, and a group `M : AddCommGrpCat.{v}` such that the restriction is
    constant: `restrict p F ≅ constant S' M`.

  Source: Brian Conrad, *Reductive group schemes* (2014),
  `conrad-2014-reductive-group-schemes`, proof of Corollary B.3.6, p.293: "We call an
  étale sheaf on a scheme isotrivial if it becomes constant over a finite étale cover."
  A "finite étale cover" is a finite étale surjective morphism. The value group `M` is an
  arbitrary abelian group in universe `v`, as in the source. No finite generation is
  required. `restrict`, `constant` and `IsEtaleSheaf` are the published definitions.

## Statements

- `isIsotrivial_constant M`: every constant sheaf `constant S M` is isotrivial. It is an
  étale sheaf by the published `isEtaleSheaf_constant`; take `p = 𝟙 S`.
- `IsIsotrivial.of_iso e hF`: isotriviality is invariant under isomorphism of presheaves.
  The sheaf condition transfers by the published `isEtaleSheaf_iff_of_iso`, and the
  trivialization is composed with the restriction of `e⁻¹`.
- `locallyConstantAddEquiv X x M`: on a preconnected space `X` with a point `x`,
  evaluation at `x` is an additive isomorphism from `LocallyConstant X M` to `M`.
- `constantSectionsAddEquiv M V x`: for `V : Over T` with preconnected source and a point
  `x`, the sections of `constant T M` over `V` are identified with `M`.
- `locallyConstantCongrRight X e` and `constantCongr T e`: an isomorphism of groups
  `e : M ≃+ N` induces isomorphisms of the groups of locally constant functions, and an
  isomorphism `constant T M ≅ constant T N` of constant sheaves.
- `nonempty_addEquiv_of_iso_of_object e V x` and `nonempty_addEquiv_of_iso e`: if
  `constant T M ≅ constant T N` and `T` is nonempty, then `M ≃+ N`. In the first form it
  suffices to have one object `V` over `T` whose source is preconnected and has a
  point.
- `nonempty_addEquiv_of_apply_eq ef eg a b hab`: suppose `F` is constant with group `M`
  over `f : X ⟶ S` and with group `N` over `g : Y ⟶ S`, and the images of `f` and `g`
  meet (`f a = g b`). Then `M ≃+ N`.
- `exists_common_model hF` (**one coefficient group on a connected base**): if `S` is a
  connected space and `IsFinitelyGeneratedLocallyConstant F`, then there is one finitely
  generated group `M` and an étale cover `𝒰` of `S` with
  `restrict (𝒰.f i) F ≅ constant (𝒰.X i) M` for every member `i`.

## Correspondence with the source

Conrad, proof of Corollary B.3.6, p.294: "the isomorphism type of the geometric stalk
`F_s` is locally constant in `s` for the Zariski topology on `S`. Thus, by connectedness
of `S`, there exists a finitely generated abelian group `M` so that `F_{S'} ≃ M_{S'}` for
some étale cover `S' → S`." `exists_common_model` is this statement. Its proof works with
the images of the cover members rather than with geometric stalks. These images are open
because étale morphisms are open. Two members whose images meet have isomorphic groups,
by `nonempty_addEquiv_of_apply_eq`.

## Proofs

- `locallyConstantAddEquiv`: a locally constant function on a preconnected space is
  constant (`LocallyConstant.eq_const`), so the constant function `const X m` is an
  inverse of evaluation at `x`.
- `constantCongr`: on each object the isomorphism is
  `constantSections`, then post-composition with `e` (`LocallyConstant.map`), then the
  inverse of `constantSections`. Naturality holds by definition.
- `nonempty_addEquiv_of_iso`: choose a point `t` of `T` and use the object
  `Spec κ(t) ⟶ T` (`T.fromSpecResidueField t`), whose source has exactly one point.
  Evaluate the given isomorphism there and use `constantSectionsAddEquiv` on both sides.
- `nonempty_addEquiv_of_apply_eq`: Mathlib's `Scheme.Pullback.exists_preimage_pullback`
  gives a point of `X ×_S Y`. Over this nonempty fibre product, the two trivializations
  give `constant M ≅ constant N`. The chain of isomorphisms uses `restrictConstantIso`,
  `restrictIso`, `restrictCompIso` and `restrictCongrIso` along
  `pullback.condition`. Then apply `nonempty_addEquiv_of_iso`.
- `exists_common_model`: take the given cover with groups `M i`, and fix a member `i₀`
  whose image contains a chosen point of `S`. Let `W₁` be the union of the images of the
  members with `M i ≃+ M i₀`, and `W₂` the union of the images of the others. Both are
  open, and they cover `S`. They are disjoint by the previous item. So `W₁` is clopen and
  nonempty, hence all of `S`, since `S` is connected. The members of the first kind
  therefore already cover `S`. They form an étale cover (`Scheme.Cover.mkOfCovers`), on
  which `F` is constant with group `M i₀` after composing with `constantCongr`. The
  covering property of the original cover is read off with
  `Scheme.presieve₀_mem_precoverage_iff`.
