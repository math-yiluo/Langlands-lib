import Langlands.ClassFieldTheory.Local.FiniteUnramifiedConnecting
import Langlands.ClassFieldTheory.Local.FiniteUnramifiedFrobenius
import Langlands.ClassFieldTheory.Local.FiniteUnramifiedLocalField
import Langlands.ClassFieldTheory.Local.UnramifiedInvariantInflationProof

noncomputable section

open Langlands.LocalField Langlands.LocalGalois.Separable ValuativeRel

namespace Langlands.ClassFieldTheory.Local

universe u

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

section FiniteStage

variable (E : IntermediateField F (SeparableClosure F)) [FiniteDimensional F E] [IsGalois F E]
  (hE : ArithmeticUnramified F E)

local instance spectralUnramifiedInvariantNormedE : NontriviallyNormedField E := FiniteExtension.normedField F E
local instance spectralUnramifiedInvariantValuativeRelE : ValuativeRel E := FiniteExtension.valuativeRel F E
local instance spectralUnramifiedInvariantLocalFieldE : IsNonarchimedeanLocalField E := FiniteExtension.isLocalField F E
local instance spectralUnramifiedInvariantValuativeExtensionF : ValuativeExtension F E := spectralFiniteExtension_valuativeExtension F E
local instance spectralUnramifiedInvariantDegreeNonzero : NeZero (Module.finrank F E) := ⟨Module.finrank_pos.ne'⟩

/-- The finite relative invariant with the actual arithmetic residue Frobenius. -/
def spectralUnramifiedInvariant : relativeCohomology F E 2 →+ RationalModIntegers :=
  finiteLocalUnramifiedInvariant F E (spectralFiniteExtension_algebraMap_continuous F E)
    (localRamificationFactor_eq_one_of_arithmeticUnramified F E hE)
    (finiteUnramifiedCyclicCoordinate F E hE)

theorem spectralUnramifiedInvariant_injective :
    Function.Injective (spectralUnramifiedInvariant F E hE) :=
  finiteLocalUnramifiedInvariant_injective F E (spectralFiniteExtension_algebraMap_continuous F E)
    (localRamificationFactor_eq_one_of_arithmeticUnramified F E hE)
    (finiteUnramifiedCyclicCoordinate F E hE)

theorem spectralUnramifiedInvariant_range :
    (spectralUnramifiedInvariant F E hE).range = denominatorSubgroup (Module.finrank F E) :=
  finiteLocalUnramifiedInvariant_range F E (spectralFiniteExtension_algebraMap_continuous F E)
    (localRamificationFactor_eq_one_of_arithmeticUnramified F E hE)
    (finiteUnramifiedCyclicCoordinate F E hE)

theorem spectralUnramifiedInvariant_cyclicClass (a : Fˣ) :
    spectralUnramifiedInvariant F E hE
      (cyclicClass F E (finiteUnramifiedCyclicCoordinate F E hE).toMonoidHom a) =
    rationalClass ((normalizedUnitOrder F (.ofMul a) : ℚ) / Module.finrank F E) :=
  finiteLocalUnramifiedInvariant_cyclicClass F E (spectralFiniteExtension_algebraMap_continuous F E)
    (localRamificationFactor_eq_one_of_arithmeticUnramified F E hE)
    (finiteUnramifiedCyclicCoordinate F E hE) a

/-- The same stage value by valuation, inverse connecting map, and arithmetic Frobenius. -/
theorem spectralUnramifiedInvariant_eq_serre (x : relativeCohomology F E 2) :
    spectralUnramifiedInvariant F E hE x =
      serreFiniteUnramifiedInvariant F E (spectralFiniteExtension_algebraMap_continuous F E)
        (localRamificationFactor_eq_one_of_arithmeticUnramified F E hE)
        (finiteUnramifiedCyclicCoordinate F E hE) x :=
  finiteLocalUnramifiedInvariant_eq_serre F E (spectralFiniteExtension_algebraMap_continuous F E)
    (localRamificationFactor_eq_one_of_arithmeticUnramified F E hE)
    (finiteUnramifiedCyclicCoordinate F E hE) x

end FiniteStage

variable (E M : IntermediateField F (SeparableClosure F)) [FiniteDimensional F E] [IsGalois F E]
  [FiniteDimensional F M] [IsGalois F M]

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The values at finite unramified stages are compatible under actual relative inflation. -/
theorem spectralUnramifiedInvariant_inflation (h : E ≤ M)
    (hE : ArithmeticUnramified F E) (hM : ArithmeticUnramified F M)
    (x : relativeCohomology F E 2) :
    letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
    letI := IsScalarTower.of_algHom (IntermediateField.inclusion h)
    spectralUnramifiedInvariant F M hM (relativeInflation F E M 2 x) =
      spectralUnramifiedInvariant F E hE x := by
  let := (IntermediateField.inclusion h).toRingHom.toAlgebra
  let := IsScalarTower.of_algHom (IntermediateField.inclusion h)
  let : NeZero (Module.finrank F E) := ⟨Module.finrank_pos.ne'⟩
  let : NeZero (Module.finrank F M) := ⟨Module.finrank_pos.ne'⟩
  let : FiniteDimensional E M := Module.Finite.of_restrictScalars_finite F E M
  let : Module.Free E M := Module.Free.of_divisionRing E M
  let χE := finiteUnramifiedCyclicCoordinate F E hE
  let χM := finiteUnramifiedCyclicCoordinate F M hM
  have hm : Module.finrank F M = Module.finrank F E * Module.finrank E M :=
    (Module.finrank_mul_finrank F E M).symm
  have hσ : (cyclicCoordinateGenerator χM).restrictNormal E = cyclicCoordinateGenerator χE := by
    dsimp only [χE, χM]
    rw [cyclicCoordinateGenerator_finiteUnramified, cyclicCoordinateGenerator_finiteUnramified]
    exact restrictNormalHom_finiteUnramifiedFrobenius F E M h hE hM
  have hχ := UnramifiedInflation.coordinate_restrict_val F E M ⟨_, hm⟩ χE χM hσ
  obtain ⟨a, rfl⟩ := exists_finiteLocal_cyclicClass F E χE x
  change spectralUnramifiedInvariant F M hM
      (relativeInflation F E M 2 (cyclicClass F E χE.toMonoidHom a)) = _
  rw [UnramifiedInflation.inflation_cyclicClass F E M hm χE.toMonoidHom χM.toMonoidHom hχ a]
  dsimp only [χE, χM]
  rw [spectralUnramifiedInvariant_cyclicClass, spectralUnramifiedInvariant_cyclicClass]
  apply congrArg rationalClass
  have hk : (Module.finrank E M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  rw [ofMul_pow, map_nsmul, nsmul_eq_mul, hm]
  push_cast
  rw [mul_comm (Module.finrank F E : ℚ), mul_div_mul_left _ _ hk]

end Langlands.ClassFieldTheory.Local
