# Flat normal schemes over a DVR are integrally closed in their generic fibre

Worker 6.

- `localization_normal_of_hasNormalStalks`: if a scheme has normal stalks (Library
  `HasNormalStalks`), then for an affine open `U` and a prime `p` of `Γ(X, U)`, the localization at
  `p` is an integrally closed domain (it is isomorphic to a stalk, `isLocalization_stalk'`).
- `isIso_fromNormalization_of_normal`: for `T` flat over the DVR `R` with normal stalks, the
  relative normalization of `T` in its generic fibre (Mathlib `Scheme.Hom.normalization` of
  `genericι T`) maps isomorphically to `T`. Proof: being an isomorphism is local on the target;
  over an affine open `U` the map is `Γ(T, U) → integralClosure Γ(T, U) Γ(T_K, ·)`, which is
  injective (localization at a non-zero-divisor) and surjective by criterion E3
  (`FlatDvrNormality.mem_range_of_isIntegral_of_normal`).

This is the algebraic fact behind the lifting clause of the stable model: a normal flat scheme is
integrally closed in its generic fibre (Conrad, appendix to Prasad–Yu, Corollary A.4, p.29, uses
this through the universal property of normalization).
