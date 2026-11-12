# Smoothness of the archimedean determinant factor of a Hecke character

Author: Worker 5136.

This internal module proves that, for every Hecke character `χ` of a number
field `K` and every rank `n`, the archimedean determinant factor
`x ↦ χ(det x)` is real-smooth on the archimedean matrix group, in the
Library's mixed coordinates `archimedeanGLCoordinates`. No finite-order
hypothesis is used. The Library's finite-order development obtains local
constancy of this factor from `χ.HasFiniteOrder`; for a general `χ` the factor
is not locally constant, but it is smooth, and smoothness is what the smooth
function spaces need.

## Characters of a real normed space

`exists_continuousLinearMap_exp_of_continuous_add`: a continuous function
`f : V → ℂ` on a real normed space with `f 0 = 1`, `f (x + y) = f x * f y` and
no zeros equals `exp ∘ L` for a continuous real-linear map `L : V →L[ℝ] ℂ`.
The proof lifts `f`, as a map to `ℂ \ {0}`, through the covering map
`Complex.exp` (Mathlib's `Complex.isCoveringMap_exp`) with `g 0 = 0`. The
lifts `(x, y) ↦ g (x + y)` and `(x, y) ↦ g x + g y` of the same map agree at
`(0, 0)`, so uniqueness of lifts on the connected space `V × V` gives
additivity of `g`. A continuous additive map between real normed spaces is
real-linear (`AddMonoidHom.toRealLinearMap`).

## Characters of the units of a commutative real Banach algebra

Let `A` be a commutative real Banach algebra and `ψ : Aˣ →ₜ* ℂˣ` a continuous
character.

- `banachExpUnit x` is `NormedSpace.exp x` as a unit, with inverse `exp (-x)`. It is
  continuous, `banachExpUnit 0 = 1` and `banachExpUnit (x + y) = banachExpUnit x * banachExpUnit y`
  (commutativity of `A` is used here).
- `unitsCharacterExtension ψ : A → ℂ` is `ψ` on units and `0` elsewhere. This
  extension is needed only to state smoothness on the open set of units of the
  normed space `A`. Its multiplicativity in a unit factor is
  `unitsCharacterExtension_mul_unit`.
- `exists_unitsCharacter_exp`: `ψ (banachExpUnit x) = exp (L x)` for a continuous
  real-linear `L`, by the previous section.
- `contDiffAt_unitsCharacterExtension_one`: the exponential is analytic, hence
  smooth, with derivative the identity at `0`. The smooth inverse function
  theorem (`ContDiffAt.to_localInverse`) gives a smooth local inverse `log`
  near `1`. Near `1` the extension equals `y ↦ exp (L (log y))`, which is
  smooth.
- `contDiffAt_unitsCharacterExtension`: at a unit `u`, the extension equals
  `a ↦ ψ(u) · ψ̃(u⁻¹ a)`, a constant times the composite of a continuous linear
  map with a function smooth at `1`.

## The determinant factor

`contDiff_archimedeanDet`: the determinant of `ArchimedeanMatrix K n` (matrices
over the mixed space) is a polynomial in the matrix entries
(`Matrix.det_apply'`), hence smooth.

`AdelicGL.pair_eq_ofInfinite_mul_ofFinite` writes `pair a b` as
`ofInfinite a * ofFinite b`. `AdelicGL.determinant_ofInfinite` computes the
idele determinant of `ofInfinite a` as the archimedean idele of `det a`, with
finite component `det 1 = 1`.

`HeckeCharacter.mixedCharacter χ` is the archimedean component `χ.atInfinity`
transported to the units of the mixed space through the inverse coordinate ring
isomorphism `InfiniteAdeleRing.ringEquiv_mixedSpace`. By
`adelicDeterminant_ofInfinite_coordinates`,
`χ(det (ofInfinite (coordinates⁻¹ x))) = mixedCharacter χ (det x)`.

`HeckeCharacter.contMDiff_adelicDeterminant_ofInfinite`: the function
`x ↦ χ(det (ofInfinite (coordinates⁻¹ x)))` is `ContMDiff` of all orders from
the units manifold of `ArchimedeanMatrix K n` to `ℂ`. It is the composite of the
smooth inclusion of units, the smooth determinant and the extension of
`mixedCharacter χ`, which is smooth at every unit.

`HeckeCharacter.contMDiff_adelicDeterminant_pair`: for every fixed finite
component `b`, the slice `x ↦ χ(det (pair (coordinates⁻¹ x) b))` is the constant
`χ(det (ofFinite b))` times the previous function, hence smooth. This is the
form used by the Library's slice-wise smooth-function spaces.

Provenance: internal. These are standard facts about continuous characters of
real Lie groups, proved here directly. They are an ingredient for
Henniart (2000), §2.2, which twists by arbitrary quasicharacters. No
correspondence with a particular passage of the literature is claimed.
