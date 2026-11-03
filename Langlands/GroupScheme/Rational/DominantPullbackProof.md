# Proof that dominant affine maps have injective actual coordinate pullback

Author: Worker 1236.

This file proves the published proposition
`Langlands.GroupScheme.PointedCoordinateWeights.DominantPullbackStatement`
(in [`DominantPullbackStatement`](DominantPullbackStatement.md)) as the theorem

```lean
theorem Langlands.GroupScheme.PointedCoordinateWeights.dominantPullbackStatement :
    DominantPullbackStatement.{u}
```

for every universe `u`. The statement is used unchanged. Over every field
`k : Type u`, take objects `V W : Over (Spec (CommRingCat.of k))` with
`IsAffineHom V.hom` and `IsAffineHom W.hom`, and a morphism `f : V ⟶ W`.
If `IsReduced W.left` and `IsDominant f.left` hold, then the actual coordinate
pullback `pullback f : Coord W →ₐ[k] Coord V` from
[`PointedCoordinateAction`](PointedCoordinateAction.md) is injective. The
reduced-target hypothesis is used exactly as stated. The proof adds no
hypothesis on `k`, no finite type and no integrality. It uses no action and no
rational point.

## Linking the actual pullback to `Spec`

Write `e_V = coordinateIso V` and `e_W = coordinateIso W` for the chosen actual
isomorphisms `algSpec (Coord V) ≅ V` and `algSpec (Coord W) ≅ W`. The helper
theorem

```lean
theorem algSpec_map_pullback (f : V ⟶ W) :
    (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom (pullback f)).op ≫
        (coordinateIso W).hom = (coordinateIso V).hom ≫ f
```

says that, under these isomorphisms, `Spec` of the actual pullback is `f`.
Its proof unfolds the existing definitions.

- `pullback f` is `pointCoordinates (universalPoint V ≫ f)`. The inverse of
  `pointCoordinates` sends an algebra map `φ` to
  `algSpec.map (ofHom φ).op ≫ e_W.hom`. So `Equiv.symm_apply_apply` gives
  `algSpec.map (ofHom (pullback f)).op ≫ e_W.hom = universalPoint V ≫ f`.
- `universalPoint V` is the inverse of `pointCoordinates` at the identity
  algebra map. That is `algSpec.map (𝟙 _) ≫ e_V.hom = e_V.hom`, by
  `CommAlgCat.ofHom_id`, `op_id`, `Functor.map_id` and `Category.id_comp`.

## The injectivity argument

Let `ψ` be the morphism of commutative rings `Coord W ⟶ Coord V` that
`commAlgCatEquivUnder` assigns to `CommAlgCat.ofHom (pullback f)`. Its
underlying function is `pullback f` by definition. The proof of
`dominantPullbackStatement` has these steps.

1. Mathlib's `algSpec_map_left` says that the underlying scheme morphism of
   `algSpec.map (ofHom (pullback f)).op` is `Spec.map ψ`. So the left
   components of `algSpec_map_pullback` give
   `Spec.map ψ ≫ e_W.hom.left = e_V.hom.left ≫ f.left`. Cancelling `e_W`
   gives `Spec.map ψ = e_V.hom.left ≫ f.left ≫ e_W.inv.left`.
2. The scheme `Spec (Coord W)` is reduced, by `isReduced_of_isOpenImmersion`
   applied to the isomorphism `e_W.hom.left : Spec (Coord W) ⟶ W.left` and the
   hypothesis `IsReduced W.left`.
3. `Spec.map ψ` is dominant. By step 1 it is the composite of an isomorphism,
   the dominant map `f.left`, and another isomorphism. Mathlib's instances give
   dominance of isomorphisms, which are surjective, and of composites.
4. `IsSchemeTheoreticallyDominant.of_isDominant` (in
   `Mathlib/AlgebraicGeometry/Morphisms/SchemeTheoreticallyDominant.lean`)
   applies, since the target is reduced. So `Spec.map ψ` is scheme-theoretically
   dominant. It is quasi-compact because it is a morphism of affine schemes;
   instance search finds this. Mathlib's `Scheme.Hom.app_injective` at the
   open `⊤` then shows that `(Spec.map ψ).appTop` is injective.
5. `Scheme.ΓSpecIso_naturality` gives
   `ψ = (ΓSpecIso _).inv ≫ (Spec.map ψ).appTop ≫ (ΓSpecIso _).hom`. This is a
   composite of injective maps, so `ψ` is injective. Hence `pullback f` is
   injective.

Step 1 uses the specified actual presentations `coordinateIso`. So the result
is about the existing map `PointedCoordinateWeights.pullback f`, not some other
coordinate map.

## Dependencies

- Statement: `DominantPullbackStatement`
  (`Rational/DominantPullbackStatement`), which imports
  `Rational/PointedCoordinateAction` for `Coord`, `coordinateIso`,
  `pointCoordinates`, `universalPoint` and `pullback`.
- Mathlib: `algSpec_map_left`, `isReduced_of_isOpenImmersion`,
  `IsSchemeTheoreticallyDominant.of_isDominant`, `Scheme.Hom.app_injective`,
  `Scheme.ΓSpecIso_naturality`, and the instances for dominance and
  quasi-compactness.

No Library file is edited. The theorem uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Source

The target comes from Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second
edition (2015), registered source `conrad-gabber-prasad-2015-pseudo-reductive`,
SHA-256 `1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The proof of Lemma 3.3.4 (printed p.108, PDF p.134) begins: "The dominant map
`V × V′ → VV′` induces an injection `O(VV′) ↪ O(V) ⊗_k O(V′)`." There `VV′`
is the closure of the image of `V × V′`, with `V` and `V′` geometrically
integral, so the target `VV′` is reduced. The book gives no separate argument
for this injection. The Lean route through scheme-theoretic
dominance is this project's own.
