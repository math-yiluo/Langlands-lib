# Determinant multiplication by any Hecke character on smooth adelic functions

Author: Worker 5136.

This internal module restricts the Library's multiplier
`ContinuousRationalFunctions.determinantMultiplier n χ` (from
`Langlands.Automorphic.DeterminantMultiplier`), which multiplies a function by
`g ↦ χ(det g)`, to the published smooth spaces of
`Langlands.Automorphic.Smooth`. It does this for every Hecke character `χ`. The
Library's `SmoothDeterminantMultiplier.lean` does the same for characters of
finite order, whose determinant factor is locally constant on every slice. Here
the archimedean factor is only smooth, and the finite factor is locally constant
for every character. The number field is `F : Type u` and every rank `n`,
including zero, is allowed.

## The determinant factor

In the namespace `Langlands.Global.HeckeCharacter`:

- `heckeFiniteDeterminantKernel n χ` is the kernel of
  `d ↦ χ(det (ofFinite d))` on the finite adelic group, as an open subgroup. It
  is open by `isOpen_ker_finiteDeterminant` (module
  `Langlands.Global.HeckeDeterminantLocalConstancy`).
  `mem_heckeFiniteDeterminantKernel` states the membership criterion.
- `isLocallyConstant_adelicDeterminant_pair`: on every finite slice
  `b ↦ χ(det (a, b))` is locally constant. The slice value is the constant
  archimedean value times the finite value
  (`AdelicGL.pair_eq_ofInfinite_mul_ofFinite`), and the finite value is locally
  constant (`isLocallyConstant_finiteDeterminant_val`).
- `infiniteDeterminantCharacter n χ` is the homomorphism
  `a ↦ χ(det (ofInfinite a))` on the archimedean matrix group, with
  `infiniteDeterminantCharacter_apply`.
  `infiniteDeterminantCharacter_mem_smoothFunctions` says that its values form a
  smooth function (`contMDiff_adelicDeterminant_ofInfinite`, module
  `Langlands.Global.ArchimedeanCharacterSmoothness`).
- `adelicDeterminant_pair_val`: the value at `(a, b)` is the finite value at `b`
  times the archimedean value at `a`.

## Preservation of the smooth spaces

In the namespace `Langlands.Automorphic`:

- `infiniteSmooth_heckeDeterminantMultiplier`: slice-wise smoothness on the
  infinite slices is preserved. On each infinite slice the factor is smooth
  (`contMDiff_adelicDeterminant_pair`), and the product of two smooth functions
  is smooth (`contDiff_mul`). A local canonical completeness instance on the
  archimedean matrix type lets Lean find the Library's charts on the units; it
  changes neither the norm nor the topology.
- `finiteLocallyConstant_heckeDeterminantMultiplier`: on each finite slice both
  factors are locally constant, so their product is.
- `smooth_heckeDeterminantMultiplier` combines the two.
- `finiteSmooth_heckeDeterminantMultiplier`: if an open subgroup `L` fixes `f`,
  then `L ⊓ heckeFiniteDeterminantKernel n χ` fixes the product. This uses the
  Library's covariance `determinantMultiplier_rightAction`,
  `R(g) M_χ f = χ(det g) M_χ R(g) f`.
- `hasFiniteLevel_heckeDeterminantMultiplier`: a compact open finite level is
  kept, by the Library's `finiteSmooth_hasFiniteLevel` applied to the new open
  stabilizer and the old compact level.
- `finiteSmoothRational_heckeDeterminantMultiplier`: the smooth space with one
  common open finite stabilizer is preserved.
- `determinantMultiplier_map_eq_of_preserves`: a submodule preserved by the
  multipliers of `χ` and `χ⁻¹` is its own image under the multiplier of `χ`.
  The inverse formula is the Library's `determinantMul_inv_apply`.

## The restricted automorphisms

`SmoothRationalFunctions.heckeDeterminantMultiplier n χ` and
`FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ` are continuous
complex-linear automorphisms of the two smooth spaces, obtained with
`ContinuousLinearEquiv.ofSubmodules` from the previous item. For each of them,
`evaluate_heckeDeterminantMultiplier` gives multiplication by `χ(det g)`,
`evaluate_heckeDeterminantMultiplier_symm` gives multiplication by its inverse,
and `heckeDeterminantMultiplier_rightAction` is the covariance
`R(g) M_χ = χ(det g) M_χ R(g)`. The four local additive instances are the
canonical submodule structures.

Provenance: internal. The smoothness of `χ ∘ det` is part of the route sketched
in the Markdown of `Langlands.Automorphic.HeckeDeterminantTwistStatement` for
Henniart (2000), §2.2. No correspondence with a particular passage of the
literature is claimed. This module does not treat differential operators, the
center, growth or automorphy. Those are in the other `HeckeTwist` modules.
