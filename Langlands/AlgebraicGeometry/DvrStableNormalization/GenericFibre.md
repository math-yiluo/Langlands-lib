# Generic fibres of schemes over a discrete valuation ring

Namespace `Langlands.AlgebraicGeometry.DvrStableNormalization`. Let `R` be a DVR.

- `sec r`: the global section of `Spec R` given by `r`.
- `isOpenImmersion_generic`: `Spec (FractionRing R) → Spec R` is an open immersion (Library
  `isOpenImmersion_spec_fractionRing_of_dvr`).
- `opensRange_generic`: its image is the basic open of a uniformizer `ϖ`.
- `genericι Z`: for `Z` over `Spec R`, the actual generic fibre inclusion
  `pullback Z.hom (Spec.algebraMap R (FractionRing R)) ⟶ Z.left` (first projection).
- `pullSec Z r`, `resSec Z r U`: the pulled-back global section and its restriction to `U`.
- `opensRange_genericι`: the generic fibre is the basic open of `pullSec Z ϖ`.
- `isLocalization_app_of_opensRange_eq`: for any open immersion `j : W → Z` whose image is the
  basic open `D(f)` of a global section, and any affine open `U`, the ring map
  `j.app U : Γ(Z, U) → Γ(W, j⁻¹ U)` makes the target a localization away from `f|_U`
  (via `IsAffineOpen.isLocalization_of_eq_basicOpen` and `appIso`).
- `isLocalization_genericι_app`: the special case of the generic fibre.
- `resSec_mem_nonZeroDivisors`: for flat `Z`, the restriction of a uniformizer to an affine open is
  a non-zero-divisor (flatness of `R → Γ(Z, U)`).

Internal scheme-theoretic toolkit, no separate literature claim.
