# Full faithfulness of the actual Picard square gluing comparison

This module proves that the published comparison functor

```
PicardGroupoid.squareGluingComparison i₁ i₂ j₁ j₂ w :
  PicardGroupoid Y ⥤ PicardGroupoid.SquareGluingData i₁ i₂
```

is fully faithful under two explicit hypotheses. The setting is an arbitrary
commuting square of schemes in one universe `u`,

```
i₁ : Y₀ ⟶ Y₁,  i₂ : Y₀ ⟶ Y₂,  j₁ : Y₁ ⟶ Y,  j₂ : Y₂ ⟶ Y,
w : i₁ ≫ j₁ = i₂ ≫ j₂.
```

No field, properness, closedness or nilpotence hypothesis is assumed here. The
functor is the actual one from the published `InfinitesimalGluing` module. It
sends an actual line bundle `L` on `Y` to its two ordinary pullbacks and the
ordinary overlap isomorphism `PicardGroupoid.squarePullbackIso`.

Namespace: `Langlands.AlgebraicGeometry.Picard.SquareGluingFullyFaithful`.

## The two hypotheses

`AffineRestrictedCubes i₁ i₂ j₁ j₂ : Prop` says the following. For every
affine open `U` of `Y` there are a scheme `T₀` and morphisms

- `ι₁ : T₀ ⟶ j₁ ⁻¹ᵁ U`, `ι₂ : T₀ ⟶ j₂ ⁻¹ᵁ U` and `g₀ : T₀ ⟶ Y₀`,

with `ι₁ ≫ (j₁ ⁻¹ᵁ U).ι = g₀ ≫ i₁` and `ι₂ ≫ (j₂ ⁻¹ᵁ U).ι = g₀ ≫ i₂`. In
addition the square of global-section ring maps

```
IsPullback (j₁ ∣_ U).appTop (j₂ ∣_ U).appTop ι₁.appTop ι₂.appTop
```

is a pullback in `CommRingCat`. So `Γ(U, 𝒪)` is the fibre product of the
global sections of the two inverse images over those of `T₀`.

For the relative affine square of the target statement, the published
`InfinitesimalAffineOpenSquare.appTop_isPullback` supplies this hypothesis.
There `T₀ = (i₁ ≫ j₁) ⁻¹ᵁ U`, `ι₁` and `ι₂` are its `leftRestriction` and
`rightRestriction`, and `g₀` is the open inclusion.

`CommonAffineTrivializingCovers Y : Prop` says the following. For every two
actual line bundles `L` and `L'` on `Y` there are an index type `ι : Type u`
and opens `U : ι → Y.Opens` with:

- each `U i` affine;
- `iSup U = ⊤`; and
- nonempty isomorphisms from the pullbacks of `L.obj` and `L'.obj` along
  `(U i).ι` to `structureModule (U i).toScheme`.

The published `LineBundle.exists_commonAffineTrivializingCover` gives exactly
this statement for every scheme.

## Main results

- `unitsJointlyInjectiveOnOpens`: `AffineRestrictedCubes i₁ i₂ j₁ j₂` implies
  the published `TwoLegIsoGluing.UnitsJointlyInjectiveOnOpens j₁ j₂`.
- `existsUnique_iso`: assume both hypotheses and let `L L' : LineBundle Y`.
  Take isomorphisms `e₁ : j₁^* L ≅ j₁^* L'` and `e₂ : j₂^* L ≅ j₂^* L'` of
  ordinary module pullbacks. Assume they agree over `Y₀` in the following
  sense:

  ```
  i₁^*(e₁.hom) ≫ (squarePullbackIso j₂ i₁ i₂ j₁ w L'.obj).hom =
    (squarePullbackIso j₂ i₁ i₂ j₁ w L.obj).hom ≫ i₂^*(e₂.hom).
  ```

  Then there is a unique isomorphism `E₀ : L.obj ≅ L'.obj` with
  `(pullback j₁).mapIso E₀ = e₁` and `(pullback j₂).mapIso E₀ = e₂`.
- `fullyFaithful i₁ i₂ j₁ j₂ w hR hcov` is a
  `Functor.FullyFaithful` structure on `squareGluingComparison i₁ i₂ j₁ j₂ w`.
  Here `hR` and `hcov` are the two hypotheses. `full` and `faithful` are its
  `Full` and `Faithful` consequences.

Helper results:

- `eq_of_isPullback`: two elements of the apex of a ring pullback are equal
  when both projections agree on them.
- `appTop_comp_apply`: the actual `appTop` of a composite, evaluated on an
  element.
- `eqToHom_iso_hom_hom`: the underlying module map of the arrow of an actual
  Picard groupoid given by an equality of objects.
- `squarePullbackIso_app`: the underlying module map of the component of
  `PicardGroupoid.squarePullbackIso` at `L` is the hom of the module-level
  `Langlands.Scheme.Modules.squarePullbackIso j₂ i₁ i₂ j₁ w L.of.obj`.
- `leftIso` and `rightIso` are the two module isomorphisms of the legs of an
  arrow between comparison objects. `leftIso_compatible` is the arrow's
  `Comma` equation, rewritten as the compatibility condition above.

## Implemented proof

`unitsJointlyInjectiveOnOpens` applies the published affine reduction
`unitsJointlyInjectiveOnOpens_of_affine`. Let `t : T ⟶ Y` be an open immersion
with `T` affine. Take two units of `Γ(T, ⊤)` with equal images on both fibre
products. Let `U` be the open range of `t`, which is affine. Transport the
units to `Γ(U, ⊤)` along the inverse of `t.isoOpensRange`. The canonical map
`j ⁻¹ᵁ U ⟶ pullback j t`, given by `pullback.lift`, carries the hypothesis to
equal images under `(j ∣_ U).appTop` for `j = j₁, j₂`. The ring pullback from
`AffineRestrictedCubes` and `eq_of_isPullback` make the transported units
equal. Hence the original units are equal. Only the ring pullback of the
hypothesis is used here, not the two corner equations.

`existsUnique_iso` chooses the cover given by `CommonAffineTrivializingCovers`
for `L` and `L'` and forms the open cover `Y.openCoverOfIsOpenCover`. It then
applies the published `TwoLegIsoGluing.existsUnique_iso_of_local`. The
unit-injectivity input is `unitsJointlyInjectiveOnOpens`. The local
trivializations come from the cover. For the local compatible lifts, fix a
member `U i`. Take the cube from `AffineRestrictedCubes` and derive
`ι₁ ≫ (j₁ ∣_ U i) = ι₂ ≫ (j₂ ∣_ U i)` from its corner equations and `w`. Then
apply the published `SquareLocalIsoLift.exists_compatible_lift`. Its side faces
are the cartesian squares `isPullback_morphismRestrict` for `j₁` and `j₂`, and
its top square is the ring pullback of the hypothesis.

`fullyFaithful` takes an arrow `φ` of gluing data. It applies
`existsUnique_iso` to `leftIso φ`, `rightIso φ` and `leftIso_compatible φ`. The
preimage is the chosen isomorphism, promoted to an arrow of the actual Picard
groupoid with `ObjectProperty.isoMk` and `Core.isoMk`. `map_preimage` follows
from the two pullback equations by `Comma.hom_ext`, `Core.hom_ext` and
`ObjectProperty.hom_ext`. `preimage_map` follows from the uniqueness clause,
since the image of an arrow `a` has legs `(pullback jᵢ).mapIso` of `a`.

## Provenance

This is internal content. It is a local-to-global argument: isomorphisms of
line bundles are determined and glued locally, and on affine opens the rings
of sections form pullbacks. It is assembled from published Library
interfaces: `TwoLegIsoGluing`, `SquareLocalIsoLift` and `InfinitesimalGluing`.
No cited source theorem is formalized.

## Scope

This module proves only full faithfulness. Essential surjectivity of the
comparison and the exact field infinitesimal gluing statement are not proved
here.
