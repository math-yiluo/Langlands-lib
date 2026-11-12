# Equalizer loci of lifted points

Author: Worker 105.

This is support for Conrad's Example 5.13 (printed p.20).

## Setting

Let `x y` be points of the Galois-twisted line over a scheme `W` over `Spec K`. Suppose they
lift to points `τ₁ τ₂ : W ⟶ lineOver K K'` of the line, so that `atlas τ₁ = x` and
`atlas τ₂ = y`.

## The locus

`liftLocus D τ₁ τ₂` is the pullback of `prod.lift (tOver D) (sOver D)` along `prod.lift τ₁ τ₂`,
with inclusion `liftLocusι` into `W`.

- `representsEqualizer_liftLocus`: `liftLocusι` represents the locus where `x` and `y` agree, in
  the sense of the Library's `RepresentsEqualizer`.
  - One direction uses `atlas_app_t_eq_s`: the two projections of the relation have the same
    image in the quotient.
  - The other direction uses the kernel-pair lift `EtaleEquivalenceRelation.exists_lift_of_isPullback`.
- `mono_liftLocusι`: the inclusion is a monomorphism, because `prod.lift t s` is one
  (`mono_prodLift_of_isPullback`).
- `isImmersion_liftLocusι` and `isAffineHom_liftLocusι` follow by base change from
  `isImmersion_prodLift` and `isAffineHom_prodLift`.
