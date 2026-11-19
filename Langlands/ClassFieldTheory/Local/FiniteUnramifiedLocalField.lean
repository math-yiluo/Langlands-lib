import Langlands.ClassFieldTheory.Local.LocalFieldIntegerExtension
import Langlands.ClassFieldTheory.Local.SpectralResidueBaseChange
import Langlands.Galois.Local.SeparableUnramifiedProof
import Langlands.LocalField.FiniteExtension

/-! # Local-field structures and ramification on separable unramified stages -/

noncomputable section

open IsLocalRing Langlands.LocalField Langlands.LocalGalois Langlands.LocalGalois.Separable
open ValuativeRel
open scoped NNReal

namespace Langlands.ClassFieldTheory.Local

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]

local instance finiteUnramifiedLocalFieldBaseNormedField : NontriviallyNormedField K := localNormedField K
local instance finiteUnramifiedLocalFieldBaseUltrametric : IsUltrametricDist K := localNormedField_ultrametric K
local instance finiteUnramifiedLocalFieldBaseComplete : CompleteSpace K := localNormedField_complete K
local instance finiteUnramifiedLocalFieldResidueFinite : Finite (ResidueField (baseIntegers K)) := localResidue_finite K

section FiniteExtension

variable (X : Type u) [Field X] [Algebra K X] [FiniteDimensional K X]

/-- The chosen spectral valuation relation respects the original base relation. -/
theorem spectralFiniteExtension_valuativeExtension :
    letI := FiniteExtension.valuativeRel K X
    ValuativeExtension K X := by
  let := FiniteExtension.valuativeRel K X
  exact ⟨FiniteExtension.algebraMap_vle_iff K X⟩

/-- The actual algebra embedding is continuous for the chosen spectral topology. -/
theorem spectralFiniteExtension_algebraMap_continuous :
    letI := FiniteExtension.normedField K X
    Continuous (algebraMap K X) := by
  let := FiniteExtension.normedField K X
  let := FiniteExtension.normedAlgebra K X
  exact continuous_algebraMap K X

/-- The intrinsic integer ring for the chosen spectral relation is the
spectral valuation subring. -/
def spectralFiniteExtensionIntegerEquiv :
    letI := FiniteExtension.valuativeRel K X
    𝒪[X] ≃+* extensionIntegers K X := by
  let := FiniteExtension.valuativeRel K X
  let : (spectralValuation K X).Compatible := Valuation.Compatible.ofValuation _
  exact RingEquiv.subringCongr (by
    ext x
    change valuation X x ≤ 1 ↔ spectralValuation K X x ≤ 1
    exact ((valuation X).vle_one_iff).symm.trans (spectralValuation K X).vle_one_iff)

end FiniteExtension

variable (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E]

/-- For an arithmetic-unramified stage, the intrinsic residue cardinality
is the base cardinality raised to its field degree. -/
theorem spectralFiniteExtensionResidue_card (hE : ArithmeticUnramified K E) :
    letI := FiniteExtension.valuativeRel K E
    Nat.card 𝓀[E] = Nat.card 𝓀[K] ^ Module.finrank K E := by
  let := FiniteExtension.valuativeRel K E
  calc
    Nat.card 𝓀[E] = Nat.card (ResidueField (extensionIntegers K E)) :=
      Nat.card_congr (ResidueField.mapEquiv (spectralFiniteExtensionIntegerEquiv K E)).toEquiv
    _ = Nat.card (ResidueField (baseIntegers K)) ^
        Module.finrank (ResidueField (baseIntegers K))
          (ResidueField (extensionIntegers K E)) := Module.natCard_eq_pow_finrank
    _ = Nat.card 𝓀[K] ^ Module.finrank K E := by
      rw [Nat.card_congr (localResidueEquiv K).toEquiv,
        (arithmeticUnramified_iff_residue_finrank K E).mp hE]

/-- Arithmetic unramifiedness gives intrinsic ramification factor one for
the actual spectral local-field structure. -/
theorem localRamificationFactor_eq_one_of_arithmeticUnramified
    (hE : ArithmeticUnramified K E) :
    letI := FiniteExtension.normedField K E
    letI := FiniteExtension.valuativeRel K E
    letI := FiniteExtension.isLocalField K E
    letI := spectralFiniteExtension_valuativeExtension K E
    localRamificationFactor K E = 1 := by
  let := FiniteExtension.normedField K E
  let := FiniteExtension.valuativeRel K E
  let := FiniteExtension.isLocalField K E
  let := spectralFiniteExtension_valuativeExtension K E
  have hf : localResidueDegree K E = Module.finrank K E :=
    Nat.pow_right_injective (show 1 < Nat.card 𝓀[K] from Finite.one_lt_card)
      ((localResidue_card K E).symm.trans (spectralFiniteExtensionResidue_card K E hE))
  have hd := localRamificationFactor_mul_residueDegree K E
    (spectralFiniteExtension_algebraMap_continuous K E)
  apply Nat.eq_of_mul_eq_mul_right (Module.finrank_pos (R := K) (M := E))
  rw [one_mul]
  simpa only [hf] using hd

section Tower

variable (L X Y : Type u) [Field L] [Field X] [Field Y]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [ValuativeExtension K L]
    [Algebra K X] [FiniteDimensional K X]
    [Algebra L Y] [FiniteDimensional L Y]
    [Algebra K Y] [IsScalarTower K L Y] (f : X →ₐ[K] Y)

local instance finiteUnramifiedLocalFieldUpperNormedField : NontriviallyNormedField L := localNormedField L
local instance finiteUnramifiedLocalFieldUpperUltrametric : IsUltrametricDist L := localNormedField_ultrametric L
local instance finiteUnramifiedLocalFieldUpperComplete : CompleteSpace L := localNormedField_complete L

private theorem spectralEmbedding_le_one (x : X) :
    spectralValuation L Y (f x) ≤ 1 ↔ spectralValuation K X x ≤ 1 := by
  constructor
  · intro hx
    by_contra h
    have hv : 1 < spectralValuation K X x := lt_of_not_ge h
    have hx0 : x ≠ 0 := by
      intro hzero
      simp [hzero] at hv
    have hinv : spectralValuation K X x⁻¹ < 1 := by
      rw [map_inv₀]
      exact inv_lt_one_of_one_lt₀ hv
    let a : extensionIntegers K X := ⟨x⁻¹, hinv.le⟩
    let b : extensionIntegers L Y := ⟨f x, hx⟩
    let g := spectralExtensionIntegerMap K L X Y f
    have hab : g a * b = 1 := by
      apply Subtype.ext
      change f x⁻¹ * f x = 1
      rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
    have hg : IsUnit (g a) := ⟨⟨g a, b, hab, (mul_comm b (g a)).trans hab⟩, rfl⟩
    exact hinv.ne ((Separable.isUnit_iff_eq_one _ a).mp (isUnit_of_map_unit g a hg))
  · intro hx
    exact (spectralExtensionIntegerMap K L X Y f ⟨x, hx⟩).property

set_option backward.isDefEq.respectTransparency false in
/-- A compatible embedding between finite extensions respects the two
chosen spectral valuation relations. -/
theorem spectralFiniteEmbedding_valuativeExtension :
    letI := FiniteExtension.valuativeRel K X
    letI := FiniteExtension.valuativeRel L Y
    letI := f.toRingHom.toAlgebra
    ValuativeExtension X Y := by
  let := FiniteExtension.valuativeRel K X
  let := FiniteExtension.valuativeRel L Y
  let := f.toRingHom.toAlgebra
  refine ⟨fun x y => ?_⟩
  change spectralValuation L Y (f x) ≤ spectralValuation L Y (f y) ↔
    spectralValuation K X x ≤ spectralValuation K X y
  by_cases hy : y = 0
  · subst y
    simp
  have hyX : 0 < spectralValuation K X y :=
    pos_iff_ne_zero.mpr ((map_ne_zero _).mpr hy)
  have hyY : 0 < spectralValuation L Y (f y) :=
    pos_iff_ne_zero.mpr ((map_ne_zero _).mpr ((map_ne_zero f).mpr hy))
  calc
    spectralValuation L Y (f x) ≤ spectralValuation L Y (f y) ↔
        spectralValuation L Y (f (x / y)) ≤ 1 := by
      rw [map_div₀, map_div₀, div_le_one₀ hyY]
    _ ↔ spectralValuation K X (x / y) ≤ 1 := spectralEmbedding_le_one K L X Y f _
    _ ↔ spectralValuation K X x ≤ spectralValuation K X y := by
      rw [map_div₀, div_le_one₀ hyX]

end Tower

end Langlands.ClassFieldTheory.Local
