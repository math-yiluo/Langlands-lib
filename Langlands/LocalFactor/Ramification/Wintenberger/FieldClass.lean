import FontaineWintenberger.LocalField.Basic
import Langlands.Galois.Local.AbsoluteDefinitions
import Langlands.LocalField.Definitions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact

/-!
# The field class of the FontaineWintenberger library on local fields

A nontrivially normed ultrametric field whose closed balls are compact is a complete
discretely valued field with finite, hence perfect, residue field of prime characteristic:
a field of `FontaineWintenberger.IsPerfectResidueLocalField`. This applies to `Padic p` with
its norm, to every `PadicField` with its canonical spectral norm, and to every Mathlib
nonarchimedean local field with the Library's normed-field adapter.
-/

noncomputable section

namespace Langlands.Ramification.Wintenberger

universe u

open scoped NormedField NNReal in
/-- A proper nonarchimedean nontrivially normed field satisfies the standing hypothesis of the
FontaineWintenberger library: its unit ball is a discrete valuation ring and its residue field
is finite, hence perfect of prime characteristic. -/
theorem isPerfectResidueLocalField_of_properSpace (K : Type*) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ProperSpace K] :
    FontaineWintenberger.IsPerfectResidueLocalField K := by
  have : (Valued.v : Valuation K ℝ≥0).RankOne :=
    inferInstanceAs (NormedField.valuation (K := K)).RankOne
  have hcpt : CompactSpace (Valued.integer K) := by
    apply isCompact_iff_compactSpace.mp
    convert isCompact_closedBall (0 : K) 1 using 1
    ext x
    simp [Valued.integer.mem_iff]
  obtain ⟨-, hd, hf⟩ :=
    (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
      (K := K) (Γ₀ := ℝ≥0)).mp hcpt
  have : IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring := hd
  have : Finite (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring) := hf
  have : FontaineWintenberger.IsCompleteDiscreteValuedField K := {}
  have : PerfectField (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring) :=
    inferInstance
  exact
    { residueChar_prime :=
        (CharP.char_is_prime_or_zero
          (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring) _).resolve_right
          (CharP.char_ne_zero_of_finite
            (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring) _) }

/-- A finite-dimensional normed algebra over a locally compact complete ultrametric field, whose
norm is ultrametric, is a field of the FontaineWintenberger library. -/
theorem isPerfectResidueLocalField_of_finiteDimensional (K₀ : Type*) [NontriviallyNormedField K₀]
    [CompleteSpace K₀] [LocallyCompactSpace K₀] (K : Type*) [NontriviallyNormedField K]
    [IsUltrametricDist K] [NormedAlgebra K₀ K] [FiniteDimensional K₀ K] :
    FontaineWintenberger.IsPerfectResidueLocalField K := by
  have : ProperSpace K₀ := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K₀
  have : ProperSpace K := FiniteDimensional.proper K₀ K
  exact isPerfectResidueLocalField_of_properSpace K

/-- The `p`-adic numbers with their norm are a field of the FontaineWintenberger library. -/
instance padic_isPerfectResidueLocalField (p : ℕ) [Fact p.Prime] :
    FontaineWintenberger.IsPerfectResidueLocalField (Padic p) :=
  isPerfectResidueLocalField_of_properSpace (Padic p)

/-- The spectral norm of a finite extension of `Padic p` is ultrametric. -/
theorem padicField_isUltrametricDist {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) :
    letI := F.canonicalNormedField
    IsUltrametricDist F.Carrier :=
  let := F.canonicalNormedField
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := Padic p) (L := F.Carrier))

/-- A `p`-adic field with its canonical spectral norm is a field of the FontaineWintenberger
library. -/
theorem padicField_isPerfectResidueLocalField {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) :
    letI := F.canonicalNormedField
    FontaineWintenberger.IsPerfectResidueLocalField F.Carrier :=
  let := F.canonicalNormedField
  let := F.canonicalNormedAlgebra
  let := padicField_isUltrametricDist F
  isPerfectResidueLocalField_of_finiteDimensional (Padic p) F.Carrier

/-- Every Mathlib nonarchimedean local field, with the Library's normed-field adapter, is a
field of the FontaineWintenberger library. -/
theorem localField_isPerfectResidueLocalField (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    letI := LocalGalois.localNormedField K
    FontaineWintenberger.IsPerfectResidueLocalField K :=
  let := LocalGalois.localNormedField K
  let := LocalGalois.localNormedField_ultrametric K
  have : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  isPerfectResidueLocalField_of_properSpace K

end Langlands.Ramification.Wintenberger
