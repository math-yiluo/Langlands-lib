# Semilinearity of the relative reduced norm over a number field

Module: `Langlands.Algebra.CentralSimple.LandherrNumberFieldNorm`.

- `finiteCompletion_unitaryInvolutionSplitting`: every finite completion `F_v` of a number
  field has the unitary splitting property `UnitaryInvolutionSplitting` (module
  `Langlands.Algebra.UnitaryInvolutionStatements`). The completion is a nonarchimedean local
  field (`Global.FiniteCompletion.isNonarchimedeanLocalField`), and the property follows from
  `Algebra.CentralSimple.unitaryDivisionSplitting` and `localUnitaryDivisionCommutative`
  (modules `Langlands.Algebra.CentralSimple.UnitaryDivisionSplitting` and
  `Langlands.Algebra.LocalUnitaryDivisionCommutativeProof`).
- `exists_finitePlace_not_isSquare`: for a separable quadratic extension `E/F` of a number
  field, `d = skewSq F E` is not a square in some finite completion; otherwise it would be a
  square in `F` by `QuadraticNormLocalGlobal.isSquare_of_all_finite`, contradicting
  `not_isSquare_skewSq`.
- `relNorm_baseChange`: for `B` a finite-dimensional central simple `E`-algebra and
  `τ : FirstKindInvolution F B` acting on `E` by the conjugation, the relative reduced norm
  satisfies `relNorm R (τ_R z) = tensorConj (relNorm R z)` for every commutative `F`-algebra
  `R` and every `z ∈ R ⊗_F B`. Apply `relNorm_baseChange_of_nonsplit` (module
  `Langlands.Algebra.CentralSimple.LandherrNormSemilinear`) with a finite completion in which
  `d` is not a square.

## Provenance

The classical identity `Nrd(τ x) = σ(Nrd x)` for involutions of the second kind, obtained
here from the local splitting of
unitary algebras at a nonsplit finite place. It is used in the reduction of Landherr's
theorem to elements of relative reduced norm one.
