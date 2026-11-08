# The reduced induced closed subscheme on a closed set

Author: Worker 1038.

Module `Langlands.AlgebraicGeometry.ReducedSubscheme`, namespace
`Langlands.AlgebraicGeometry.ReducedSubscheme`.

For a closed set `Z` of a scheme `X`, Mathlib's ideal sheaf
`Scheme.IdealSheafData.vanishingIdeal Z` cuts out a closed subscheme `subscheme` with closed
immersion `subschemeι`. This module records three facts about it.

## Results

- `isReduced_vanishingIdeal_subscheme Z`: the subscheme is reduced. On an affine open `U` the
  ideal is `PrimeSpectrum.vanishingIdeal` of a set of primes, so it is radical
  (`PrimeSpectrum.isRadical_vanishingIdeal`). The quotient ring is therefore reduced
  (`Ideal.isRadical_iff_quotient_reduced`), and so is its spectrum. The subscheme has the
  open cover `subschemeCover.openCover` by these spectra, and `IsReduced.of_openCover`
  concludes.
- `range_subschemeι_vanishingIdeal Z`: the range of `subschemeι` is `Z`. It combines
  Mathlib's `range_subschemeι` with `coe_support_vanishingIdeal`.
- `exists_lift_vanishingIdeal g Z h`: let `T` be a reduced scheme and `g : T ⟶ X` a
  quasi-compact morphism whose range lies in `Z`. Then `g` factors through `subschemeι`.

  The proof shows that the vanishing ideal is contained in the kernel `g.ker`. Let `s` be a
  section on an affine open `U` that lies in the vanishing ideal. Since `T` is reduced, it
  suffices that the basic open of `g^* s` is empty (`eq_zero_of_basicOpen_eq_bot`), i.e. that
  `s` vanishes at each point `g t`. The point `g t` lies in `Z`. Its prime in
  `Spec Γ(X, U)` (`IsAffineOpen.primeIdealOf`) therefore lies over `Z`, so it contains `s` by
  `PrimeSpectrum.mem_vanishingIdeal`. That is the claim, by `fromSpec_preimage_basicOpen`.

  The factorization is Mathlib's `g.toImage` followed by
  `Scheme.IdealSheafData.inclusion` of the inequality of ideal sheaves.

## Provenance

Internal helper for task 13a3a0fd. The facts are the standard properties of the reduced
induced closed subscheme structure on a closed set: it is reduced, has the given support,
and every morphism from a reduced scheme landing in the set factors through it. Here the
factorization is stated for quasi-compact morphisms, the case Mathlib's `Hom.toImage`
covers. The Lean proof is built from Mathlib's ideal-sheaf API and transcribes no source
proof.
