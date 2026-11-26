# A common centre annihilator for smoothings in an irreducible cuspidal summand

Module `Langlands.Automorphic.GeneralLinearSummandCenterAnnihilation`. It applies the abstract
centre finiteness theorem `ArchimedeanGL.exists_ideal_smoothingFamily_eq_zero`
(module `Langlands.Automorphic.GeneralLinearHilbertCenterFinite`) to the right regular
representation on `L²` of the positive-central rational quotient `Q` of `GL_{r+1}` over a number
field `F`, and to the archimedean smoothings of
`Langlands.Automorphic.GeneralLinearSummandSmoothing`.

## Setting

`S` is the full almost-everywhere cuspidal subspace `fullAEL2CuspidalSubmodule` of `L²(Q, μQ)`
and `πc` its right action `fullAEL2CuspidalBoundedRightAction`. `P` is a submodule of `S`
invariant under `πc`. `ρ` is the right action `haarQuotientL2BoundedRightAction` on all of
`L²(Q, μQ)`. `ν` is a Haar measure on the archimedean group `InfiniteAdelicGL F (r+1)` for a
Borel structure, and the archimedean group is assumed second countable.

## Definitions

- `archimedeanUnitsPoint F r`: the archimedean units `(ArchimedeanMatrix F (r+1))ˣ`, mapped to the
  adelic points of the group scheme through `archimedeanGLCoordinates`,
  `AdelicGL.ofInfinite` and the inverse of `GeneralLinearGroupPoints.adelicHomeomorph`.
  `archimedeanUnitsPoint_coordinates` identifies it on coordinates with
  `archimedeanAdelicPoint`.
- `summandSubmodule F r hPD T i hi I e hc P`: the image `P.map S.subtype` of `P` in
  `L²(Q, μQ)`.
- `unitsKernel F r κ`: a kernel `κ : ArchimedeanGL.SmoothCompactKernel` transported to the
  units. `unitsHaar F r ν`: the image of `ν` on the units, a Haar measure
  (`unitsHaar_isHaarMeasure`).

## Results

- `mul_archimedeanUnitsPoint`: every adelic point `g` normalizes the archimedean points,
  `g · a = (g∞ a g∞⁻¹) · g` with `g∞` the archimedean coordinate of `g`. Hence
  `haarQuotientL2BoundedRightAction_normalizes`: each `ρ g` normalizes the archimedean
  restriction of `ρ`.
- `haarQuotientL2BoundedRightAction_archimedean_isContinuous`: the archimedean restriction is
  jointly continuous, from the Library's `haarQuotientL2JointRightAction`.
- `inner_haarQuotientL2BoundedRightAction`: `ρ` preserves the inner product.
- `isClosed_summandSubmodule`, `summandSubmodule_invariant`: if `P` is closed, its image is
  closed, and it is `ρ`-invariant.
- `summandSubmodule_minimal`: if `P` is minimal among nonzero closed `πc`-invariant submodules
  of `S`, its image is minimal among closed `ρ`-invariant submodules of `L²(Q, μQ)`. A closed
  invariant `W` below the image pulls back to a closed invariant submodule of `S` below `P`.
- `smoothedClass_one_eq_integral_units`: `smoothedClass … 1 κ u` equals
  `∫ unitsKernel κ (g⁻¹) • ρ(g) u` for the transported measure; this is the change of variables
  `integral_map_equiv`.
- `hasDerivAt_smoothedClass_units`: the derivative formula `hasDerivAt_smoothedClass`, along
  the exponential curves written in units coordinates.
- `smoothedClass_family_eq_zero`: the family `a ↦ smoothedClass … a κ u` satisfies the
  hypotheses of the abstract theorem: it lies in a closed invariant `A`, it is additive and
  complex-linear (`smoothedClass_add`, `smoothedClass_smul`), its value at `1` is the units
  integral, and it has the exponential-curve derivatives. Here `u ∈ A` must have a continuous
  representative invariant under an open subgroup of the finite adelic group.
- `exists_ideal_smoothedClass_eq_zero`: **main result.** Let `P` be nonzero, closed and minimal
  among nonzero closed `πc`-invariant submodules of `S`. Then there is an ideal `J` of the
  enveloping centre of finite complex codimension with the following property. Let `u` lie in
  the image of `P` and have a continuous representative `h` invariant under right translation
  by an open subgroup of the finite adelic group. Then for every kernel `κ` and every `z ∈ J`,
  `smoothedClass … (centerInclusion z) κ u = 0`.

## Provenance

This is a step towards the centre finiteness of the forms attached to an irreducible cuspidal
summand, used in `Langlands.Automorphic.GeneralLinearSummandFormsNonzero`. In Getz and Hahn,
*An Introduction to Automorphic Representations* (2024), the comparison (9.40) in the proof of
Theorem 9.7.3, printed pp. 265–266 (PDF pp. 277–278), places the `K`-finite vectors in the
automorphic forms through the proof of Theorem 6.6.4, printed p. 172 (PDF p. 186). There
`Z(g)`-finiteness comes from admissibility: an irreducible admissible `(g, K∞)`-module has an
infinitesimal character (Corollary 4.6.3, printed p. 125, PDF p. 140). Here it comes from the
unitary Schur argument of `GeneralLinearHilbertCenterFinite`. The module does not prove growth,
compact finiteness or cuspidality.
