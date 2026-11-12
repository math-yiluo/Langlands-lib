# Proof that action quotients over a field are quasi-separated and finitely presented

Authors: Worker 193 and Worker 3749.

`Langlands.AlgebraicGeometry.AlgebraicSpace.actionQuotientFiniteness` proves the
published `ActionQuotientFinitenessStatement.{u}` for every universe `u`. The statement
and its Lean/Markdown pair are unchanged. Let `k` be a field, `G` a group scheme over `k`
with `G.X.hom` quasi-compact, and `b : SchemeAction G Z` an action on a scheme `Z` that is
locally of finite type and quasi-compact over `k`. Let `X` be an algebraic space over `k`
that is locally of finite type, and `π : h_Z ⟶ X` an fppf action quotient of `b` that is
smooth and surjective. Then `X` is quasi-separated and `FinitePresentationOverRing k X`
holds. The final theorem combines the two results below,
`ActionQuotientFiniteness.isQuasiSeparated` and
`ActionQuotientFiniteness.finitePresentationOverRing`. The helper module
`ActionQuotientOrbitRelation` is part of this contribution.

All auxiliary declarations are in the namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace.ActionQuotientFiniteness`.

## Descent lemmas for smooth maps

The Library has these lemmas for étale atlases only. The proofs here are copies with
"étale" replaced by "smooth"; they use only that base changes of the atlas are flat,
locally of finite presentation and surjective.

- `isPullback_snd_map_id`, `relative_prod_map` and
  `quasiCompact_descendsAlong_surjective_inf_quasiCompact` expose the content of
  private declarations in
  `FinitePresentationRelationQuotient.lean`. `relative_prod_map` says that a product
  `f × g` of maps that are relatively `P` (representable with base changes in `P`) is
  relatively `P`. The descent theorem says that quasi-compactness descends along surjective
  quasi-compact morphisms of schemes.
- `relative_of_isSmooth_isSurjective` is
  `SmoothRelationQuotientReduction.relative_of_isEtale_isSurjective` with a smooth
  surjective `A` in place of an étale one. Let `f : F ⟶ G` be a representable map of
  presheaves and `P` a property of morphisms of schemes that is stable under base change
  and descends along fppf coverings. If the base change of `f` along one smooth surjective
  map `A` from a scheme is a morphism of schemes with `P`, then `f` is relatively `P`. For
  a test map `T ⟶ G`, the base change of `A` to `T` is a smooth surjective scheme map
  `pT`. The base change of `f` to `T`, pulled back along `pT`, is a base change of the
  given morphism with `P`. So `P` descends along `pT`.
- `isQuasiSeparated_of_smooth_cover` is `FinitePresentationRelationQuotient.isQuasiSeparated_of_atlas`
  for a smooth surjective `a : h_U ⟶ X`. Let `R = U ×_X U` with projections `t, s`. If
  `(t, s) : R ⟶ U × U` is quasi-compact, then `X` is quasi-separated. Proof:
  `isPullback_kernel_diagonal` makes `(t, s)` the base change of the diagonal of `X` along
  `a × a : h_U × h_U ⟶ X × X`. That map is smooth and surjective by `relative_prod_map`.
  Quasi-compactness descends along fppf coverings: the descent theorem gives descent
  along surjective, flat, quasi-compact maps (`DescendsAlong.of_le`), and Mathlib's
  instance for properties local at the target extends this to surjective, flat maps
  locally of finite presentation. Apply `relative_of_isSmooth_isSurjective` with `P = QuasiCompact` and
  `f = diag X`; the diagonal is representable because `X` is an algebraic space.
  The fppf descent step is also named `quasiCompact_descendsAlong_fppf`;
  `surjective_descendsAlong_fppf` supplies descent of surjectivity.

## Quasi-separatedness

`isQuasiSeparated`. Let `R` be the kernel pair of `p = π.hom`, formed with the
representability of `p`, with projections `t, s : R ⟶ Z`. Its square is a pullback of `p`
against itself, and `s` is smooth. The cofork equation of `IsFppfActionQuotient` gives
`b.hom ≫ p = snd ≫ p` on `G × Z`. So there is `orbitMap : G × Z ⟶ R` with `orbitMap ≫ t = b.hom` and
`orbitMap ≫ s = snd`.

`orbitMap` is surjective on points. Let `r` be a point of `R`. The `R`-points `t` and `s` of `Z`
have equal images in `X` (`app_eq_iff_of_isPullback`). By
`ActionQuotientOrbitRelation.orbitSieve_mem`, the sieve of the `f : V ⟶ R` with
`f ≫ t = b.act g (f ≫ s)` for some `g` is fppf covering. By
`ActionQuotientOrbitRelation.exists_mem_range_of_mem`, such an `f` has `r = f(v)` for some
point `v`. The map `lift g (f ≫ s) ≫ γ` equals `f`: both agree after `t` and after `s`,
and the square is a pullback. So `r` is the image under `orbitMap` of the image of `v` in
`G × Z`.

`G × Z` is quasi-compact: `G` is quasi-compact over the affine `Spec k` and `Z ⟶ Spec k`
is quasi-compact, so the fibre product is quasi-compact. Thus `R`, the image of `G × Z`
under the surjection `orbitMap`, is quasi-compact. `R ⟶ Spec k` is `s` followed by `Z ⟶ Spec k`,
a smooth map followed by one locally of finite type. So it is locally of finite type,
and `R` is locally Noetherian (`LocallyOfFiniteType.isLocallyNoetherian`). Being
quasi-compact, `R` is Noetherian, so every morphism out of `R` is quasi-compact
(`quasiCompact_of_noetherianSpace_source`), in particular `(t, s) : R ⟶ Z × Z`.
`isQuasiSeparated_of_smooth_cover` concludes.

## Finite presentation

`exists_affine_atlas_of_compactSpace` copies `AlgebraicSpace.exists_affine_atlas`
(`EtaleEquivalenceRelationPresentation.lean`), replacing its hypothesis that the source
of the surjective map `c` is affine by the hypothesis that it is quasi-compact. That was
the only use of affineness. It also returns the comparison map. Let `a : h_U ⟶ Y` be
étale and surjective and `c : h_V ⟶ Y` surjective with `V` quasi-compact. Let
`ρ : U ×_Y V ⟶ V` be the base change of `a`, which is étale and surjective. The images
under `ρ` of the preimages of the affine opens of `U` are open (étale maps are open) and
cover `V`. Finitely many cover `V`, so they come from a finite family of affine opens
`U_i` of `U`. Their disjoint union `U₀` is affine, and `j : U₀ ⟶ U` is étale. The
composite `h_{U₀} ⟶ Y` is étale (`isEtale_map`, `IsEtale.comp`). It is surjective by
`isSurjective_of_isPullback`, because its base change along `c` is surjective on points.

`finitePresentationOverRing`. Take an étale surjective atlas `a : h_U ⟶ X` with `U`
locally of finite type over `k`. `Z` is quasi-compact, and `c = π.hom` is surjective. The
previous lemma gives an affine `U₀` and an étale `j : U₀ ⟶ U` such that `h_{U₀} ⟶ X` is
an étale surjective atlas. `U₀ ⟶ Spec k` is `j` followed by `U ⟶ Spec k`, so it is
locally of finite type. Over the Noetherian `Spec k` this is local finite presentation
(`LocallyOfFinitePresentation.iff_locallyOfFiniteType`). It is quasi-compact because
`U₀` and `Spec k` are affine. So `X` has an atlas with
`LocallyOfFinitePresentation ⊓ QuasiCompact`, which is `FinitePresentationOverRing k X`.

## Provenance

The route follows the derivation in the statement's Markdown
(`ActionQuotientFinitenessStatement.md`). The copied lemmas come from the Library
modules named above. The names of the declarations are internal.

## Additional smooth-cover helpers

Worker 3749's independently accepted contribution supplies the following helpers.
Its identical smooth descent and quasi-separatedness lemmas are shared above.
Both reviewed proofs establish the same unchanged `actionQuotientFiniteness`;
the combined module uses the final assembly described above.

## The action graph covers the kernel pair (section `Action`)

- `pointRel_iff` and `pointRel_equivalence`: on `T`-points, the relation generated by the pair
  `(b.hom, snd) : G × Z ⇉ Z` from `RelationQuotient` (`EtaleRelationQuotient.lean`) says that
  `x` is a translate `g · y`. This relation is already an equivalence relation, by the group
  laws `act_one` and `act_mul` and the inverse of `g`.
- `exists_covering_act`: if two points `x, y : T → Z` have the same image under an fppf action
  quotient `π`, then fppf-locally on `T` there is `g` with `g · y = x`. The cofork of `π` is a
  colimit, so the map from `Z` to the sheafified point quotient `RelationQuotient.quotientSheaf`
  factors through `π`. Hence `x` and `y` agree in the sheafification of the point-quotient
  presheaf. `Presheaf.equalizerSieve_mem` gives a covering sieve on which their classes agree
  in the presheaf quotient. Since the relation is already an equivalence relation, this means
  they are related.
- `surjective_of_kernelPair`: suppose `t, s : R ⇉ Z` is the kernel pair of `π`, and
  `φ : G × Z → R` lifts `(b.hom, snd)`. Then `φ` is surjective. Apply `exists_covering_act`
  to the universal pair `(t, s)`. Every member of the resulting covering sieve factors through
  `φ` as `(g, f ≫ s)`. Pass to a scheme cover subordinate to the sieve; every point of `R`
  comes from one of its members, so it lies in the image of `φ`.

## Finite presentation from a smooth cover (section `FinitePresentation`)

`finitePresentation_of_smooth_cover` shows the following. Let `X` be locally of finite type
over `k`, with étale surjective atlas `a : U → X` locally of finite type over `k`, and let
`π : Z → X` be smooth and surjective from a quasi-compact `Z`. Then `X` is of finite
presentation over `k`.

Form `W = U ×_X Z`. The projection `p : W → Z` is étale (hence open) and surjective, and the
projection `q : W → U` is smooth (hence open). The sets `p(V)`, with `V` an affine open of `W`,
cover the compact `Z`, so finitely many suffice. The union `O` of the corresponding images
`q(V)` is a quasi-compact open of `U`. The restriction `a' : O → X` is étale. Its base change
along `π` is surjective, since each point of `Z` lies in some `p(V)` and the chosen point of
`V` maps into `O`. Surjectivity of `a'` then descends by `relative_of_isSmooth_isSurjective`.
Finally, `O → Spec k` is locally of finite presentation, because over a field locally of finite
type implies locally of finite presentation. It is also quasi-compact, so `O` is the required
atlas.


The target's sources are Conrad's Example 5.5 and Stacks Definition 65.13.2(3),
as recorded in `ActionQuotientFinitenessStatement.md`.
