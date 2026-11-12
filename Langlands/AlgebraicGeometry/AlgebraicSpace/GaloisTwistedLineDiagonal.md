# The diagonal of the Galois-twisted line

Author: Worker 105.

This module proves clauses (1) and (2) of Conrad's Example 5.13 (printed p.20) for the
Galois-twisted line `space D`:

- the diagonal is representable with every represented projection an affine immersion
  (`relative_diag`);
- the space is quasi-separated (`isQuasiSeparated`);
- it is locally of finite type over `Spec K` (`locallyOfFiniteTypeOverBase`).

These results assume `[Module.Finite K K']`. Conrad says the diagonal "is easily checked to be a
quasi-compact immersion (even affine)". The argument below supplies that check.

## General lemmas

- `EqualizerLocus.representsEqualizer_pullback`: the base change of an equalizer locus along `g`
  represents the equalizer of the restrictions along `g`.
- `EqualizerLocus.prop_of_representsEqualizer`: two monomorphisms representing the same
  equalizer locus are isomorphic over the base. So they share every property invariant under
  isomorphism.
- `AffineHomDescent.prop_of_isPullback`: such a property transfers between pullbacks of the same
  cospan.
- `AffineHomDescent.isAffineHom_of_isPullback`: affineness descends along finite surjective
  morphisms.
  - Let `U` be an affine open of the target. The preimage of `U` in the base-changed source is
    affine.
  - It maps finitely and surjectively onto the preimage of `U` in the source, which is therefore
    affine. This uses the Library's `Langlands.GroupScheme.AffineQuotient.isAffine_of_finite_surjective`.

## The equalizer loci

Let `x y` be points over a scheme `W` over `Spec K`.

- **`exists_isImmersion`.** Consider the sieve where both points lift to the line. It is the
  intersection of two image sieves of the locally surjective quotient map, so it is fppf
  covering. On it the equalizer locus is `liftLocus`, an immersion. The Library's
  `exists_representsEqualizer_of_fppf_local` glues these to an immersion `ι` representing the
  equalizer over `W`.
- **`isAffineHom_of_representsEqualizer`.** Let `ι` be any monomorphism representing the
  equalizer. Base change along `W_{K'} = W ×_K Spec K' → W` (`extOver`, `extMap`), which is
  finite and surjective.
  - `W_{K'}` has a `K'`-structure. By `exists_local_lift₂`, every point of `W_{K'}` has an open
    neighbourhood `V` on which both points lift.
  - Over `V`, the base change of `ι` and `liftLocus` represent the same equalizer, so the base
    change is affine there.
  - `IsAffineHom` is Zariski-local on the target, so the base change of `ι` to `W_{K'}` is
    affine. Finite surjective descent then shows that `ι` is affine.
- `exists_affineImmersion` combines the two. `relative_diag` and `isQuasiSeparated` apply the
  Library criterion `relative_diag_of_representsEqualizer`; affine morphisms are quasi-compact.

## Local finite type

`lineBase` is of finite type because `K'[X]` is a finitely generated `K`-algebra when `K'` is
finite over `K` (`locallyOfFiniteType_lineBase`). Then `atlas D` is an étale surjective atlas
with this structure map.
