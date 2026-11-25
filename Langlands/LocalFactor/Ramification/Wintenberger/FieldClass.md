# Local fields as fields of the FontaineWintenberger library

Module `Langlands.LocalFactor.Ramification.Wintenberger.FieldClass`, namespace
`Langlands.Ramification.Wintenberger`.

The FontaineWintenberger library works over a nontrivially normed field `K` with the class
`FontaineWintenberger.IsPerfectResidueLocalField K`: the norm is ultrametric and complete, the unit
ball `𝒪[K]` (the valuation subring of `NormedField.valuation`) is a discrete valuation ring, and
its residue field is perfect of prime characteristic. This file shows that the Library's local
fields belong to this class.

## Main statements

- `isPerfectResidueLocalField_of_properSpace (K : Type*) [NontriviallyNormedField K]
  [IsUltrametricDist K] [ProperSpace K] : FontaineWintenberger.IsPerfectResidueLocalField K`.
  Closed balls are compact, so the unit ball, which is Mathlib's `Valued.integer K` for the
  valuation of the norm, is a compact subring. Mathlib's
  `Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField`
  then gives that it is a discrete valuation ring with finite residue field. A finite field is
  perfect, and its characteristic is a prime (`CharP.char_is_prime_or_zero`,
  `CharP.char_ne_zero_of_finite`). Completeness of `K` follows from properness.
- `isPerfectResidueLocalField_of_finiteDimensional (K₀ : Type*) [NontriviallyNormedField K₀]
  [CompleteSpace K₀] [LocallyCompactSpace K₀] (K : Type*) [NontriviallyNormedField K]
  [IsUltrametricDist K] [NormedAlgebra K₀ K] [FiniteDimensional K₀ K] :
  FontaineWintenberger.IsPerfectResidueLocalField K`: a finite-dimensional normed space over a
  proper field is proper (`FiniteDimensional.proper`).
- `padic_isPerfectResidueLocalField (p : ℕ) [Fact p.Prime] :
  FontaineWintenberger.IsPerfectResidueLocalField (Padic p)`, an instance, from Mathlib's
  `ProperSpace ℚ_[p]`.
- `padicField_isUltrametricDist {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) :
  letI := F.canonicalNormedField; IsUltrametricDist F.Carrier`, from
  `isNonarchimedean_spectralNorm`.
- `padicField_isPerfectResidueLocalField {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) :
  letI := F.canonicalNormedField; FontaineWintenberger.IsPerfectResidueLocalField F.Carrier`:
  a `p`-adic field with its canonical norm, the spectral norm over `Padic p`
  (`PadicField.canonicalNormedField`, `PadicField.canonicalNormedAlgebra`).
- `localField_isPerfectResidueLocalField (K : Type u) [Field K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
  letI := LocalGalois.localNormedField K; FontaineWintenberger.IsPerfectResidueLocalField K`:
  every Mathlib nonarchimedean local field, in either characteristic, with the Library's normed
  field adapter. The adapter keeps the given topology (`LocalGalois.localNormedField_topology`
  holds by `rfl`), so local compactness gives properness.

## Declarations used

From the FontaineWintenberger library: `FontaineWintenberger.IsCompleteDiscreteValuedField`,
`FontaineWintenberger.IsPerfectResidueLocalField`. From the Library: `PadicField`,
`PadicField.canonicalNormedField`, `PadicField.canonicalNormedAlgebra`,
`LocalGalois.localNormedField`, `LocalGalois.localNormedField_ultrametric`.

## Sources

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
applications*, Ann. Sci. ENS 16 (1983), introduction: all local fields considered are complete
for a discrete valuation with perfect residue field of characteristic `p`. Serre, *Local Fields*,
Chapter II, §1: a local field in the narrow sense (finite residue field) is locally compact, and
conversely.
