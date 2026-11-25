# Transport of integral closures in localizations

Namespace `Langlands.CommutativeAlgebra.IntegralClosureTransfer`.

- `isIntegral_map_of_comm`: a ring isomorphism `G : L₁ ≃+* L₂` compatible with a ring isomorphism
  `e : A' ≃+* C` of base rings sends elements integral over `A'` to elements integral over `C`
  (map a monic polynomial along `e`).
- `integralClosureEquiv`: the induced ring isomorphism `integralClosure A' L₁ ≃+* integralClosure C L₂`;
  `integralClosureEquiv_algebraMap` records compatibility with the base maps.
- `transfer`: let `E : A' ≃ₐ[R'] C`, `r : R'`, `L₁` a localization of `A'` away from the image
  of `r`, and `L₂` a localization of `C` away from the image of `r`. Suppose the integral closure
  of `A'` in `L₁` is a finite `A'`-module and reduced after `F ⊗[R'] -` for every field `F : Type v`
  under `R'`. Then the same holds for the integral closure of `C` in `L₂`, for any `R'`-algebra
  structure on that closure which factors through `C` (hypothesis `hcomp`). The isomorphism of
  localizations is `IsLocalization.ringEquivOfRingEquiv`.

Internal helper with no literature counterpart; it transports the hypotheses of
`DvrAffineReducedFibreStatement` from `R' ⊗[R] A` to the sections of an isomorphic affine scheme.
