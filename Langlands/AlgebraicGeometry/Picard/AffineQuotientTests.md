# Affine-base arrows and Artinian tests from truncations of a finite-type algebra

This internal module collects the affine and Artinian bookkeeping for a finite-type
chart `Spec T` with a rational point. All objects are over `Spec k` for a commutative
ring `k : Type u`.

## Affine-base arrows

`affineBase k A` and `affineBaseMap` are the published constructions of
`Picard.AffineFamilyDescent` and `Picard.InfinitesimalGluing`.

- `exists_affineBaseMap_eq`: every arrow `affineBase k B ⟶ affineBase k A` over
  `Spec k` is `affineBaseMap a` for some `k`-algebra map `a : A →ₐ[k] B`. This reexports the
  existing `OpennessOfVersality.exists_affineBaseMap_eq`, shared through
  `AffineBaseMaps`. The over-`Spec k` condition makes the ring map obtained
  from `Spec.map_surjective` into a `k`-algebra map.
- `affineBaseMap_injective`: `affineBaseMap` determines the algebra map.
- `mono_affineBaseMap`: a surjective algebra map gives a monomorphism of affine
  bases. `Spec` of a surjection is a closed immersion, hence a monomorphism of
  schemes, and monomorphisms are detected on underlying scheme maps.

## Local rings

`isLocalRing_of_surjective_of_isNilpotent` proves that a commutative ring with a
surjection onto a field, whose kernel consists of nilpotent elements, is local.
Elements with nonzero image are units: if `f (x * y) = 1`, then `x * y = 1 + n` with
`n` nilpotent.

## Truncation tests

Let `T` be a Noetherian `k`-algebra, `K` a field `k`-algebra, and
`εT : T →ₐ[k] K` surjective. Write `m = ker εT`.

- `augmentation εT n : T / m ^ (n + 1) →ₐ[k] K` is induced by `εT`.
  `augmentation_mk` gives its value on classes, and `augmentation_surjective`
  shows it is surjective.
- `isLocalRing_quotient` and `isArtinianRing_quotient`: `T / m ^ (n + 1)` is local
  and Artinian. Its maximal ideal is the image of `m`, whose `(n + 1)`-st power
  vanishes.
- `test εT hεT n` is the augmented Artinian test `T / m ^ (n + 1)`.
- `transition εT hεT n : test (n + 1) ⟶ test n` is the quotient map, and
  `transition_surjective` shows it is surjective.
- `level εT hεT n : base (test n) ⟶ affineBase k T` is `Spec` of the quotient map.
  `baseMap_transition_level` proves `baseMap (transition n) ≫ level (n + 1) = level n`.

## The residue point

`exists_residueField_iso` gives, for a surjection `εT : T →ₐ[k] K`, a point `u₀` of
`Spec T` and an isomorphism `e : κ(u₀) ≅ K` such that
`Spec.map εT = Spec.map e.hom ≫ fromSpecResidueField u₀`.

Apply Mathlib's `Scheme.SpecToEquivOfField` to `Spec.map εT`. This gives a point
and a field map `κ(u₀) → K` with the required factorization. By
`Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField` and
`Spec.map_injective`, its composite with `T → κ(u₀)` is `εT`. Hence the field map is
surjective; it is injective as a map of fields.
