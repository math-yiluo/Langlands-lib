# Affine finite-étale group quotient cocones

The theorem
`Langlands.AlgebraicGeometry.FiniteEtale.affineFiniteGroupQuotientCocones`
proves the published proposition `AffineFiniteGroupQuotientCocones` from
`Langlands.AlgebraicGeometry.FiniteEtale.QuotientCoconeStatements`:

```lean
theorem affineFiniteGroupQuotientCocones : AffineFiniteGroupQuotientCocones.{u}
```

The statement is used unchanged, with the universe `u`, an arbitrary affine
locally noetherian base `S`, an arbitrary finite group `G`, and an arbitrary
diagram `D : SingleObj G ⥤ Cover S`. There are no extra hypotheses. The action
need not be free or faithful, and `|G|` need not be invertible. The cocone is
built explicitly as the spectrum of the invariant global sections. All
declarations below are in `Langlands.AlgebraicGeometry.FiniteEtale` and live
in the module `AffineQuotientCoconeProof`. The module sets
`backward.isDefEq.respectTransparency false`, as `Definitions` does.

## Points of affine schemes

For an affine scheme `Z` and a ring `K`, `affinePointEquiv Z K` is the
bijection `(Spec K ⟶ Z) ≃ (Γ(Z, ⊤) ⟶ K)`. It sends `x` to
`Spec.preimage (x ≫ Z.isoSpec.hom)`, and its inverse sends `φ` to
`Spec.map φ ≫ Z.isoSpec.inv`. `SpecMap_affinePointEquiv` records that
`Spec.map (affinePointEquiv Z K x) = x ≫ Z.isoSpec.hom`.
`affinePointEquiv_comp` says postcomposition with `h : Z ⟶ W` becomes
precomposition with `h.appTop`:
`affinePointEquiv W K (x ≫ h) = h.appTop ≫ affinePointEquiv Z K x`.
Its proof uses `Scheme.isoSpec_hom_naturality` and injectivity of `Spec.map`.

## The action on global sections

The instance `isAffine_cover_left` makes the source of every cover over an
affine base affine, via `isAffine_of_isAffineHom`, because finite morphisms
are affine. In particular, every vertex of every cocone in `Cover S` is affine.

Write `coverScheme D` for the source scheme of `D.obj (SingleObj.star G)`.
`coverAction D g` is the ring map
`(D.map (SingleObj.toEnd G g)).hom.left.appTop` on `Γ(coverScheme D, ⊤)`.
Taking global sections is contravariant, so
`coverAction_mul : coverAction D (g * h) = coverAction D g ≫ coverAction D h`,
and `coverAction_one` holds. `appTop_comp_coverAction` uses `Over.w` to show
that `coverAction D g` fixes the image of `Γ(S, ⊤)`.

The type synonym `coverRing D := Γ(coverScheme D, ⊤)` is a `def`, so that its
instances do not affect `Γ`. It carries the transported commutative ring, the
`Γ(S, ⊤)`-algebra given by the structure map's `appTop`, and the left action

```lean
g • a = (coverAction D g⁻¹).hom a        -- coverRing_smul_def
```

The inverse makes this a `MulSemiringAction G (coverRing D)`. Because the
structure map is fixed, the instance `SMulCommClass G Γ(S, ⊤) (coverRing D)`
holds. The invariant ring is
`quotientRing D := FixedPoints.subalgebra Γ(S, ⊤) (coverRing D) G`.
Since `G` is closed under inversion, `mem_quotientRing_iff` says an element is
invariant exactly when every `coverAction D g` fixes it.
`quotientRingInclusion D : CommRingCat.of (quotientRing D) ⟶ Γ(coverScheme D, ⊤)`
is the inclusion. It is injective, and
`quotientRingInclusion_comp_coverAction` shows that it is fixed by each
`coverAction D g`.

## The quotient scheme and quotient map

Under `[IsAffine S]` the module defines the following.

- `quotientScheme D := Spec (CommRingCat.of (quotientRing D))`.
- `quotientMap D := (coverScheme D).isoSpec.hom ≫ Spec.map (quotientRingInclusion D)`,
  the spectrum of the invariant inclusion.
- `quotientStructure D := Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (quotientRing D))) ≫ S.isoSpec.inv`.

`quotientMap_comp_quotientStructure` shows that `quotientMap D ≫ quotientStructure D`
is the cover's structure map. The algebra map followed by the inclusion is the
structure map's `appTop`, and `Scheme.isoSpec_hom_naturality` applies.

`quotientMap_cancel` makes `quotientMap D` cancel on the left against maps
into any affine scheme `Y`. Compose with `Y.isoSpec.hom` and write both maps as
`Spec.map` of ring maps. After cancelling the isomorphism
`(coverScheme D).isoSpec.hom`, `Spec.map_injective` shows the two ring maps
agree after composing with the injective inclusion, so they are equal.

`coverMap_comp_quotientMap` gives invariance:
`(D.map (SingleObj.toEnd G g)).hom.left ≫ quotientMap D = quotientMap D`.
It follows by naturality of `isoSpec` and
`quotientRingInclusion_comp_coverAction`.

## Factorization of invariant maps

Let `ψ : coverScheme D ⟶ Z` satisfy
`hψ : ∀ g, (D.map (SingleObj.toEnd G g)).hom.left ≫ ψ = ψ`. Then `ψ.appTop`
lands in the invariant ring. `descRingHom ψ hψ : Γ(Z, ⊤) ⟶ CommRingCat.of (quotientRing D)`
is its `RingHom.codRestrict`, and `descRingHom_comp_quotientRingInclusion`
recovers `ψ.appTop`. For affine `Z`, `descMap ψ hψ := Spec.map (descRingHom ψ hψ) ≫ Z.isoSpec.inv`.
`quotientMap_comp_descMap` proves `quotientMap D ≫ descMap ψ hψ = ψ`. If also
`ψ ≫ f` is the cover's structure map, `descMap_comp_structure` proves
`descMap ψ hψ ≫ f = quotientStructure D` by `quotientMap_cancel`.
`cocone_leg_invariant` shows the leg of any cocone over `D` satisfies `hψ`.

## Finite étaleness and the colimit

Under `[IsLocallyNoetherian S]`, `Γ(S, ⊤)` is noetherian
(`isNoetherianRing_globalSections`). `coverRing D` is a finite étale
`Γ(S, ⊤)`-algebra, by `Scheme.Hom.finite_appTop` and
`HasRingHomProperty.appTop`. With `[Finite G]`, `quotientRing_finite_etale`
applies the Library theorem `invariantAlgebraFiniteEtale Γ(S, ⊤) (coverRing D) G`.
`IsFinite.SpecMap_iff` and `HasRingHomProperty.Spec_iff` then give the
`IsFinite` and `Etale` instances for `quotientStructure D`.

- `quotientCover D := cover (quotientStructure D)` is the vertex in `Cover S`.
- `quotientCoconeMap D` is the cover morphism with underlying map `quotientMap D`.
- `quotientCocone D : Cocone D` has this morphism as its leg; naturality is
  `coverMap_comp_quotientMap`.
- `quotientCoconeIsColimit D : IsColimit (quotientCocone D)`. The descended map
  for a cocone `s` has underlying morphism `descMap` applied to the leg of `s`,
  whose vertex is affine; `descMap_comp_structure` makes it a map over `S`.
  Factorization is `quotientMap_comp_descMap`. Uniqueness follows from
  `quotientMap_cancel`, because the vertex of `s` is affine.

This universal property is proved in the actual category `Cover S`, against
every cocone, using only that all covers of the affine base are affine.

## Geometric points

Fix `Ω : Type u` with `[Field Ω]` and `s : Spec (.of Ω) ⟶ S`.

- `fiberRingHom D s x := affinePointEquiv (coverScheme D) (.of Ω) x.left` for
  a geometric point `x` of the cover. It is injective (`fiberRingHom_injective`).
  It satisfies `appTop_comp_fiberRingHom`, compatibility with the base point
  `affinePointEquiv S (.of Ω) s`.
- `fiberRingHom_map` says the action becomes precomposition:
  `fiberRingHom D s ((pointFunctor s).map (D.map (SingleObj.toEnd G g)) x) = coverAction D g ≫ fiberRingHom D s x`.
- `exists_fiberRingHom` says every ring map `Γ(coverScheme D, ⊤) ⟶ Ω` compatible
  with the base point comes from a geometric point.
- `quotientFiberRingHom D s t := Spec.preimage t.left` for a geometric point
  `t` of the quotient. It is injective, and `SpecMap_quotientFiberRingHom`
  holds. `quotientFiberRingHom_map` identifies the image of `x` under the
  quotient leg with `quotientRingInclusion D ≫ fiberRingHom D s x`.
  `algebraMap_comp_quotientFiberRingHom` gives compatibility with the base point.

Assume `[IsAlgClosed Ω]`. Make `Ω` a `Γ(S, ⊤)`-algebra through
`affinePointEquiv S (.of Ω) s`. Then geometric points of the cover and of the
quotient correspond to `Γ(S, ⊤)`-algebra maps from `coverRing D` and from
`quotientRing D` to `Ω`. Apply the Library theorem
`invariantAlgebraGeometricPoints Γ(S, ⊤) (coverRing D) G Ω`.

- `quotientCocone_surjective`: the point `t` gives an algebra map from the
  invariant ring. Its surjectivity part lifts this to `coverRing D`, and
  `exists_fiberRingHom` turns the lift into a geometric point `x`. Injectivity
  of `quotientFiberRingHom` shows `x` maps to `t`.
- `quotientCocone_orbit`: two points with the same image give algebra maps that
  agree on invariants. The orbit part gives `g` with
  `F y = (F x).comp (MulSemiringAction.toAlgHom _ _ g)`. Since `g` acts through
  `coverAction D g⁻¹`, `fiberRingHom_map` identifies `y` with the image of `x`
  under `g⁻¹`. The witness is reindexed by `g ↦ g⁻¹`. Conversely, translates
  have the same image by `quotientRingInclusion_comp_coverAction`.

The final theorem packs `quotientCocone D`, `⟨quotientCoconeIsColimit D⟩`, and
these two facts into `FiniteGroupQuotientCocone D (quotientCocone D)`.

## Reusable comparisons

For the global gluing proof, the module keeps the identification of the
quotient with the spectrum of the invariant inclusion. It does this through
`quotientScheme`, `quotientMap`, `quotientStructure`, `quotientRing`,
`quotientRingInclusion`, `quotientCover`, `quotientCocone`,
`quotientCoconeIsColimit`, `quotientCocone_surjective`, `quotientCocone_orbit`,
`descMap`, `quotientMap_cancel` and `affinePointEquiv`.

## Imports and provenance

The module imports `QuotientCoconeStatements` and the Library proof modules
`InvariantAlgebraProof` and `InvariantAlgebraGeometricPointsProof`. The
construction follows the affine case of SGA 1, Exposé V: Proposition 1.1(ii)–(iii)
and Corollary 1.2, printed p.88 (PDF p.104), and Corollary 3.4, printed p.97
(PDF p.113). The source is `sga1-arxiv-math-0206203v2`, SHA256
`8e64218d356456c534eebf996940f0f957e43b54f1a080241debe12cbaf60d3c`. The
algebraic inputs come from the two Library theorems above. The scheme-level
argument here is internal: the affine colimit argument, and the translation
between geometric points and ring maps.
