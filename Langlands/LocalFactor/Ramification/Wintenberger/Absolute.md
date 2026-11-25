# Absolute upper ramification groups of the FontaineWintenberger library and of the Library

Module `Langlands.LocalFactor.Ramification.Wintenberger.Absolute`, namespace
`Langlands.Ramification.Wintenberger`.

Two developments of ramification theory meet here. The Library's filtrations
(`Langlands.Ramification.Local`, with the `Padic` wrappers) are the ones that Library statements
use. The FontaineWintenberger library has its own (`FontaineWintenberger.upperRamificationGroup`,
`FontaineWintenberger.upperRamificationGroupInfinite`), for complete discretely valued fields with
perfect residue field, on which its theory of arithmetically profinite extensions and of the field
of norms is built. This file proves that on the Library's local fields the absolute filtrations
are equal, so that results of the FontaineWintenberger library can be read in the Library's
notions.

## Main statements

Let `K₀` be nontrivially normed, ultrametric, complete and locally compact, with valuative
relation induced by its norm (`hbase`), `K` a normed extension of `K₀`
(`[NormedAlgebra K₀ K] [FiniteDimensional K₀ K]`) with
`[FontaineWintenberger.IsCompleteDiscreteValuedField K]`, and `Ω` a separable closure of `K`
with `[Algebra K₀ Ω] [IsScalarTower K₀ K Ω]`.

- `upperRamificationGroupInfinite_eq_absolute (v : ℝ) :
  FontaineWintenberger.upperRamificationGroupInfinite K Ω v =
  Local.absoluteUpperRamificationGroup K₀ K Ω hbase v`.
- `padicBaseNorm_compatible (p : ℕ) [Fact p.Prime] (a b : Padic p) :
  ‖a‖ ≤ ‖b‖ ↔ ValuativeRel.vle a b`.
- `upperRamificationGroupInfinite_eq_padic {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (v : ℝ) :
  letI := F.canonicalNormedField;
  haveI := (padicField_isPerfectResidueLocalField F).toIsCompleteDiscreteValuedField;
  FontaineWintenberger.upperRamificationGroupInfinite F.Carrier (AlgebraicClosure F.Carrier) v =
  Padic.absoluteUpperRamificationGroup F v`.
- `localBaseNorm_compatible (K : Type u) … (a b : K) : letI := LocalGalois.localNormedField K;
  ‖a‖ ≤ ‖b‖ ↔ ValuativeRel.vle a b`.
- `upperRamificationGroupInfinite_eq_local (K : Type u) [Field K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] (Ω : Type v) [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] (w : ℝ) : letI := LocalGalois.localNormedField K;
  haveI := (localField_isPerfectResidueLocalField K).toIsCompleteDiscreteValuedField;
  FontaineWintenberger.upperRamificationGroupInfinite K Ω w =
  Local.localAbsoluteUpperRamificationGroup K Ω w`.
- `localAbsoluteUpperFiniteImage (K : Type u) … (Ω : Type v) [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] : Local.AbsoluteUpperFiniteImage K Ω`: for every finite Galois subextension
  `L` and every `v ≥ −1`, the absolute upper group maps onto `Local.localUpperRamificationGroup K L v`.
  This is the first of the five statements of `Local.AbsoluteHerbrandArithmetic`, for every Mathlib
  nonarchimedean local field in either characteristic.

## Proofs

Both absolute filtrations are infima over `FiniteGaloisIntermediateField K Ω` of the preimages of
finite upper groups under the restriction `AlgEquiv.restrictNormalHom` (the Library's
`Local.absoluteFiniteRestriction` is this map with its continuity). The finite groups agree by
`Finite.upperRamificationGroup_spectral_eq_canonical`. The p-adic statement is the case
`K₀ = Padic p`, `K = F.Carrier` with its spectral norm (`PadicField.canonicalNormedAlgebra`); the
statement for a Mathlib local field is the case `K₀ = K` with `NormedAlgebra.id`. The Library's
own proofs of the norm comparisons are private; the two `…BaseNorm_compatible` theorems prove the
same propositions, which suffices because proofs of a proposition are interchangeable.

For the exact finite images, the FontaineWintenberger theorem `map_upperRamificationGroupInfinite`
(surjectivity of the restriction of the infinite upper groups onto the finite ones, by a
compactness argument, for `Ω/K` Galois with perfect residue field) is transported by the
equalities above; `Local.localUpperRamificationGroup K L v` is by definition the canonical upper
group over the base `K` with the normed-field adapter.

## Declarations used

From the FontaineWintenberger library: `upperRamificationGroupInfinite`,
`map_upperRamificationGroupInfinite`. From the Library: `Local.absoluteUpperRamificationGroup`,
`Local.absoluteFiniteRestriction`, `Local.canonicalUpperRamificationGroup`,
`Local.localAbsoluteUpperRamificationGroup`, `Local.localUpperRamificationGroup`,
`Local.localTopologicalData`, `Local.AbsoluteUpperFiniteImage`,
`Padic.absoluteUpperRamificationGroup`, `PadicField.canonicalNormedField`,
`LocalGalois.localNormedField`, `LocalGalois.localNormedField_le`.

## Sources

Serre, *Local Fields*, Chapter IV, §3, the remark after Proposition 14 (the upper filtration of an
infinite Galois extension as the inverse limit of the finite ones; Herbrand's theorem makes the
restriction maps surjective). Wintenberger 1983, §1.1.
