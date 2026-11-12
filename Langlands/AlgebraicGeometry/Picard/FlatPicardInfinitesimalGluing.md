# Infinitesimal gluing for actual Picard groupoids over a flat base

This module generalizes the published field-base gluing theorem
`SquareGluingDescent.affineSquareComparison_isEquivalence` (module
`FieldPicardInfinitesimalGluingProof`) from a base field to an arbitrary
commutative base ring over which the scheme is flat. All declarations live in
the namespace `Langlands.AlgebraicGeometry.Picard.FlatInfinitesimalGluing`.

## Main result

```
FlatInfinitesimalGluing.affineSquareComparison_isEquivalence
  {k R A B C : Type u} [CommRing k] [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k R] [Algebra k A] [Algebra k B] [Algebra k C]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [Flat f]
  (p : R →ₐ[k] A) (q : R →ₐ[k] B) (a : A →ₐ[k] C) (b : B →ₐ[k] C)
  (h : IsPullback (ofHom p) (ofHom q) (ofHom a) (ofHom b))
  (hb : Function.Surjective b) (hn : IsNilpotent (RingHom.ker b)) :
  (PicardGroupoid.affineSquareComparison f p q a b h).IsEquivalence
```

In words: let `k` be any commutative ring and `X` a scheme flat over `Spec k`.
Let `R = A ×_C B` be a pullback of commutative `k`-algebras (the four algebra
maps form a pullback square of commutative rings), where `b : B → C` is
surjective with nilpotent kernel. Then the published comparison functor
`PicardGroupoid.affineSquareComparison f p q a b h`, which sends an actual line
bundle on `X_R` to its restrictions to `X_A` and `X_B` together with the
canonical isomorphism of their restrictions to `X_C`, is an equivalence of
groupoids. So actual line bundles and actual isomorphisms glue across such
squares. This is the gluing input for Schlessinger-type conditions on Picard
deformations over a flat base; the module is an internal generalization of
the published field-base result, not a transcription of a literature source.

The same result is packaged as data in the definition

```
FlatInfinitesimalGluing.affineSquareGluingEquivalence f p q a b h hb hn :
  PicardGroupoid X_R ≌
    PicardGroupoid.SquareGluingData ((relativeSpace f).map (affineBaseMap a))
      ((relativeSpace f).map (affineBaseMap b))
```

(where `X_R = (relativeSpace f).obj (affineBase k R)`), the equivalence of
groupoids whose functor is the published comparison
(`affineSquareGluingEquivalence_functor`, by definition). This is the entry
declaration of the unit.

No properness or finiteness hypothesis is needed. Over a field every scheme is
flat, so this recovers the field case.

## Provenance and route

The proof is the published field-base proof, verbatim, with `[Field k]`
replaced by `[CommRing k]` and the instance `[Flat f]`. In the field-base
proof the field was used at exactly one place: to know that the projection
`X_R → Spec R` is flat, in the published
`InfinitesimalCartesianCube.baseProjection_flat`. Here that flatness follows
from `[Flat f]`, since `X_R → Spec R` is the base change `pullback.fst` of `f`
(Mathlib's instance for flat base change). Every other ingredient of the field
proof (`InfinitesimalLocalEffectivity.affineSquareNeighborhood`, the full
faithfulness criterion, Čech gluing) was already stated over an arbitrary
commutative ring `k` and is reused unchanged.

## Declarations

- `baseProjection f t`: for `t : T ⟶ X_R`, the composite `T ⟶ X_R ⟶ Spec R`
  (same definition as the published field version).
- `baseProjection_flat` (instance): if `t` is an open immersion then
  `baseProjection f t` is flat. Proof: an open immersion is flat, and the
  projection `X_R ⟶ Spec R` is flat as the base change of the flat `f`.
- `cartesianCube_appTop_isPullback`: for a cartesian cube over an affine open
  immersion `t : T ⟶ X_R` (with `T` affine) into the base-changed square, the
  global section rings of `T`, `T₁`, `T₂`, `T₀` form a pullback square. The
  proof is the field-base proof, applying the published
  `InfinitesimalAffineOpenSquare.affineCube_appTop_isPullback` (flat base change
  of a ring pullback) with the flat map `baseProjection f t`.
- `affineSq f p q a b h`: the square of relative spaces `X_C, X_A, X_B, X_R` with
  the base-changed maps, as a `SquareGluingDescent.Sq`; `affineSq_C` says its
  comparison functor is, by definition, `PicardGroupoid.affineSquareComparison`.
  These do not use flatness.
- `affineRestrictedCubes`: every cartesian open cube into `affineSq` satisfies
  `SquareGluingFullyFaithful.AffineRestrictedCubes` (proof: compose with the
  inclusion cube of an affine open, then `cartesianCube_appTop_isPullback`).
- `ffOnCart`: the comparison is full and faithful on every cartesian open cube
  into `affineSq`, by `SquareGluingFullyFaithful.full`/`faithful` and common
  affine trivializing covers `LineBundle.exists_commonAffineTrivializingCover`.
- `essSurj`: every actual gluing datum is realized: local effectivity at every
  point from `InfinitesimalLocalEffectivity.affineSquareNeighborhood` (uses `hb`
  and `hn`), then the published Čech gluing `Sq.exists_iso_of_effective`.
- `affineSquareComparison_isEquivalence`: full and faithful from `ffOnCart`
  applied to the published identity cube `idC` (cartesian by `cart_idC`), and
  essentially surjective by `essSurj`.
- `affineSquareGluingEquivalence`: the equivalence
  `(affineSquareComparison f p q a b h).asEquivalence` given by the previous
  theorem; `affineSquareGluingEquivalence_functor` records (by `rfl`) that its
  functor is `PicardGroupoid.affineSquareComparison f p q a b h`.

The field-free helpers `Sq.restrict`, `Sq.restrictC`, `Sq.cart_restrictC`,
`Sq.exists_iso_of_effective`, `idC` and `cart_idC` are imported from the
published `FieldPicardInfinitesimalGluingProof` module.
