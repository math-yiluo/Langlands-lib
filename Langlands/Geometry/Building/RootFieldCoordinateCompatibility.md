# Full V6 from actual root field coordinates

Author: Worker 1045.

This internal module connects two published interfaces. The first is the
structure `RootFieldCoordinates i j s a` (module
`Langlands.Geometry.Building.QuasiSplitR1RootFieldCoordinatesStatement`): finite
separable field coordinates on an actual rational root group, on which the whole
actual centralizer acts through a character. The second is the coordinate data
`RootCoordinateEquivariance v i j s φ a` that the module
`Langlands.Geometry.Building.CentralizerCoordinateCompatibility` turns into the
centralizer compatibility V6. All statements hold at an arbitrary universe `u`.

## Setting

Let `k` be a field and `v : Valuation k (WithZero (Multiplicative ℤ))`. Let `S`
be a commutative group scheme and `G`, `Z` group schemes over `Spec k`, with
`i : S.toGrp ⟶ G`, `j : Z ⟶ G`, `s : S.toGrp ⟶ Z` and a character
`a : characterLattice S`.

An element `R : RootFieldCoordinates i j s a` consists of a finite separable
extension `E = R.extension` of `k`, a group isomorphism
`e = R.equiv : Multiplicative E ≃* rootGroupPoints i a`, and a rational
character `β = R.character` of the base change `Z_E` whose restriction along the
base change of `s` is the base change of `a`, such that for all `z ∈ Z(k)` and
`x ∈ E`

```text
j(z) e(x) j(z)⁻¹ = e(β(z_E) x),
```

where `z_E` is the image of `z` in `Z(E)`. The V6 interface uses the opposite
convention `j(z)⁻¹ e(x) j(z) = e(β(z_E)⁻¹ x)`.

## Declarations

In namespace `Langlands.Geometry.Building`:

- `RootFieldCoordinates.conj_inv R z x`: for `z ∈ Z(k)` and `x ∈ E`,
  `j(z)⁻¹ e(x) j(z) = e(β(z_E)⁻¹ x)`, where `β(z_E)⁻¹` is the inverse in the
  unit group `Eˣ`, coerced to `E`.
- `RootFieldCoordinates.toRootCoordinateEquivariance R hw hφ`: for a valuation
  `w : AddValuation E (WithTop ℝ)` with `hw : IntegerValuation.IsNormCalibrated v w`
  and a root function family `φ` with `hφ : φ_a(e(x)) = w(x)` for all `x ∈ E`,
  the coordinate data `IntegerValuation.RootCoordinateEquivariance v i j s φ a`
  with field `E`, valuation `w`, multiplicity `1` and character `β`.
- `RootFieldCoordinates.toRootCoordinateEquivarianceHenselian hH R hφ`: for
  `hH : HenselianLocalRing v.valuationSubring`, the same data with `w` the
  published induced valuation `FieldTheory.henselianSeparableAddValuation v hH E`
  of the finite separable extension `E`; the hypothesis `hφ` is
  `φ_a(e(x)) = w(x)` for this `w`.

In namespace `Langlands.Geometry.Building.IntegerValuation`, with `hH` as above:

- `isCentralizerCompatible_of_rootFieldCoordinates hH hj h hc` (needs
  `IsAffineHom G.X.hom`, affine `S` and `Z`, and `i` a monomorphism): let
  `hj : (torusCentralizer i).IsRepresentedBy j` and
  `h : Function.Bijective (Cartan.restrictionEvaluation s)`. If for every
  `a ∈ relativeRoots i` there is `R : RootFieldCoordinates i j s a` with
  `φ_a(R.equiv x) = henselianSeparableAddValuation v hH R.extension x` for all
  `x`, then `IsCentralizerCompatible v i j s h φ`.
- `isOmegaCompatible_of_rootFieldCoordinates hH hφ hc` (needs
  `IsAffineHom G.X.hom`, affine `S`, and `i` a monomorphism): for
  `D : KPApartmentData i (order v)`, `C : CentralizerDatum i` and
  `hφ : φ ∈ D.carrier`, if every `a ∈ relativeRoots i` has
  `R : RootFieldCoordinates i C.j C.s a` with
  `φ_a(R.equiv x) = henselianSeparableAddValuation v hH R.extension x` for all
  `x`, then `IsOmegaCompatible v D C`.

## Proofs

1. `conj_inv` applies the `conjugation` field of `R` to `z⁻¹` and rewrites
   `j(z⁻¹) = j(z)⁻¹` (by `map_inv` for `rationalPoints.map j`), `(z⁻¹)⁻¹ = z`,
   and `β((z⁻¹)_E) = β(z_E)⁻¹` (by `map_inv` for the extension of points and
   for the character evaluation).
2. `toRootCoordinateEquivariance` is the published constructor
   `RootCoordinateEquivariance.ofMulEquiv` applied to `hw`, `R.equiv`,
   `R.character`, `R.restriction`, `hφ` and `conj_inv`.
3. `toRootCoordinateEquivarianceHenselian` uses the published lemma
   `isNormCalibrated_henselianSeparableAddValuation hH E` for `hw`.
4. The two compatibility theorems apply the published
   `isCentralizerCompatible_of_rootCoordinates` and
   `isOmegaCompatible_of_rootCoordinates` to the data from step 3 on every
   relative root.

## Provenance and scope

This is internal glue between Library interfaces, with no literature claim of
its own; V6 is the Library's formalization of Kaletha–Prasad Definition 6.1.2.
The hypotheses ask for field coordinates on every relative root. The published
`QuasiSplitR1RootFieldCoordinatesStatement` asserts their existence only for
indivisible roots `a` with `2a` not a root, and is not proved; roots of a
non-reduced relative root system need other data, for example coordinate
families via `RootCoordinateEquivariance.toFamily` and
`isCentralizerCompatible_of_rootCoordinateFamilies`. The module constructs no
coordinates and no root function family.
