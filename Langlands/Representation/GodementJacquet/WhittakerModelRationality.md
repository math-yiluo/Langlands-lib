# Whittaker integrals on the coefficient model

Module `Langlands.Representation.GodementJacquet.WhittakerModelRationality`,
namespace `Langlands.GodementJacquet.WhittakerTorus.Padic`.

Let `F` be a p-adic field with its canonical topological data, `ψ` a unitary
additive character, `σ` an admissible complex representation of
`GL_(n+1)(F)`, `ℓ` a Whittaker functional for the standard character
`ψ_N = standardCharacter ψ n`, and `W = glModelFunction ψ n σ ℓ w` a function
of the coefficient model of `ℓ`.

- `glModelFunction_isWhittakerLike`: if `σ` satisfies
  `CoefficientTorusExpansion (standardCharacter ψ n) σ`, then
  `IsWhittakerLike F ψ W` holds.
- `glModel_shifted_of_converges`: assume `FiniteFunctionMellinStatement` and
  the torus expansion as above. Let `Φ` be a Schwartz–Bruhat function on all
  square matrices. Suppose that `∫ Φ(g) W(g) |det g|^s dg` converges absolutely
  for `Re s` larger than some `c`. Then the shifted integral
  `∫ Φ(g) W(g) |det g|^(s + n/2) dg` converges absolutely on a right half-plane
  and has a rational continuation in `q^(-s)`. This is the conclusion of
  `ModelWhittakerRationalityStatement` for this `Φ` and `w`.
- `modelWhittakerRationality (hWTA) (hFFM)`: from
  `WhittakerTypeAsymptoticStatement` and `FiniteFunctionMellinStatement`, it
  proves `GodementJacquet.ModelWhittakerRationalityStatement`.
- `whittakerModelComparison_of_asymptotics (hWTA) (hFFM)`: from the same two
  hypotheses, it proves `GodementJacquet.WhittakerModelComparisonStatement`, the
  target statement of the task.

## Source and provenance

The content is internal and derived. It connects the reduction modules
(`WhittakerIwasawaReduction`, `WhittakerMatrixRationality`) to the coefficient
model. Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg convolutions*,
Amer. J. Math. 105 (1983), Section (5.2), printed pages 420–421, assert the
convergence and rationality of these integrals for representations of
Whittaker type, in a section that completes results of their *Automorphic
forms on GL(3) I* (1979). The route through the Iwasawa decomposition and
torus Mellin integrals is described in `WhittakerIwasawaReduction`.
The torus expansion `CoefficientTorusExpansion` is the conclusion of
`ModelAsymptoticTransferStatement`, which is proved in the Library
(`modelAsymptoticTransfer`) from `WhittakerTypeAsymptoticStatement`.

## Proofs

`glModelFunction_isWhittakerLike` checks the four fields.

1. `continuous`: `glModelFunction_continuous`, from the smoothness of `σ`.
2. `equivariant`: `glModelFunction_equivariance`.
3. `smooth`: the model representation is admissible
   (`GodementJacquet.Padic.glModel_isAdmissible`), so some open subgroup `L`
   fixes `w`. For `k ∈ L`, `W(g k)` is the model function of the translate
   `ρ(k) w = w` at `g` (`glModelFunction_translate`).
4. `expansion`: for each `k`, apply the torus expansion to the model vector
   `ρ(k) w`. Its model function at `diag(a)` is `W(diag(a) k)` by definition.
   The finite-function condition of `CoefficientTorusExpansion` is exactly
   `IsFiniteFunction`, and its ratio coordinates are exactly `ratios F a`.

`glModel_shifted_of_converges`: convergence at `s + n/2` follows from the
hypothesis for `Re s > c − n/2`. Rationality is
`IsWhittakerLike.hasRationalContinuation` with `t = jpssShift n`.

`modelWhittakerRationality`: let `σ` be of Whittaker type for
`standardCharacter ψ n` (the nonvanishing of `ℓ` is not used). The Library
theorem `modelAsymptoticTransfer`, applied to `hWTA`, the canonical topological
data and the first alternative `θ = standardCharacter ψ n`, gives
`CoefficientTorusExpansion (standardCharacter ψ n) σ`. Whittaker type includes
admissibility, so `glModelFunction_isWhittakerLike` applies.
`IsWhittakerLike.matrixConverges` (module `WhittakerMatrixConvergence`) gives
convergence of the unshifted integrals on a right half-plane. Then
`glModel_shifted_of_converges` gives the conclusion.

`whittakerModelComparison_of_asymptotics` composes `modelWhittakerRationality`
with `GodementJacquet.whittakerModelComparison_of_rationality` (module
`WhittakerModelInclusion`).

## Hypotheses

The theorems keep `WhittakerTypeAsymptoticStatement` and
`FiniteFunctionMellinStatement` as explicit hypotheses `hWTA` and `hFFM`.
The Library proves both: `FiniteFunctionMellinStatement` as
`Langlands.RankinSelberg.finiteFunctionMellin` (module
`Langlands.Representation.RankinSelberg.FiniteFunctionMellinProof`) and
`WhittakerTypeAsymptoticStatement` as `Langlands.whittakerTypeAsymptotic`
(module `Langlands.Representation.Whittaker.TypeAsymptoticProof`). This module
does not import those proofs. The module
`Langlands.Representation.GodementJacquet.WhittakerModelComparisonProof`
applies `whittakerModelComparison_of_asymptotics` to them.
