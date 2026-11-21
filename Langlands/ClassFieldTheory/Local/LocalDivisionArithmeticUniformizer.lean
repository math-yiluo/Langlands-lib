import Langlands.ClassFieldTheory.Local.LocalDivisionCyclicInvariant
import Langlands.Algebra.LocalDivisionCyclicNormalization
import Langlands.Algebra.CyclicFieldNormCommutator

/-! # Arithmetic division uniformizer from the local invariant -/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

open ValuativeRel IsLocalRing CentralDivision CentralSimple LocalField
open _root_.Langlands.Brauer LocalGalois.Separable
open scoped WithZero

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Regard an irreducible element of the actual valuation integers as a field unit. -/
def localUniformizerFieldUnit {π : 𝒪[K]} (hπ : Irreducible π) : Kˣ :=
  Units.mk0 (π : K) (fun h => hπ.ne_zero (Subtype.ext h))

/-- Any uniformizer of the actual integer ring has normalized order one. -/
theorem normalizedUnitOrder_localUniformizerFieldUnit {π : 𝒪[K]} (hπ : Irreducible π) :
    normalizedUnitOrder K (.ofMul (localUniformizerFieldUnit K hπ)) = 1 := by
  let a := localUniformizerFieldUnit K hπ
  let p := localUniformizer K
  have hva : valuation K (a : K) < 1 := Valuation.integer.v_irreducible_lt_one (v := valuation K) hπ
  have ha : 0 < normalizedUnitOrder K (.ofMul a) := by
    apply (normalizedUnitOrder_pos_iff K a).mpr
    apply (Valuation.vlt_iff_lt (valuation K)).mpr
    simpa only [map_one] using hva
  have hvp : valuation K (p : K) < 1 := by
    have hp : 0 < normalizedUnitOrder K (.ofMul p) := by
      rw [normalizedUnitOrder_localUniformizer]
      exact Int.zero_lt_one
    have h := (Valuation.vlt_iff_lt (valuation K)).mp ((normalizedUnitOrder_pos_iff K p).mp hp)
    simpa only [map_one] using h
  let p₀ : 𝒪[K] := ⟨(p : K), hvp.le⟩
  have hp₀ : p₀ ∈ maximalIdeal (𝒪[K]) := (Valuation.mem_maximalIdeal_iff _ _).mpr hvp
  have hval : valuation K (p : K) ≤ valuation K (a : K) := by
    change p₀ ∈ (maximalIdeal (𝒪[K]) : Set (𝒪[K])) at hp₀
    rw [Irreducible.maximalIdeal_eq_setOfPred_le_v_coe (valuation K) hπ] at hp₀
    exact hp₀
  have hle : discreteLocalValuation K (p : K) ≤ discreteLocalValuation K (a : K) :=
    (Valuation.vle_iff_le (discreteLocalValuation K)).mp
      ((Valuation.vle_iff_le (valuation K)).mpr hval)
  rw [discreteLocalValuation_of_unit K p, discreteLocalValuation_of_unit K a,
    normalizedUnitOrder_localUniformizer, WithZero.exp_le_exp] at hle
  change normalizedUnitOrder K (.ofMul a) = 1
  omega

variable (D : Type u) [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E] [IsGalois K E]
  (hE : ArithmeticUnramified K E) (ι : E →ₐ[K] D)
  (hdegree : Module.finrank K E = CentralSimple.reducedDegree K D)

local notation "d" => CentralSimple.reducedDegree K D
local notation "σ" => finiteUnramifiedFrobenius K E hE
local notation "j" => implementingUnit ι σ

include hE in
private theorem arithmeticImplementingUnit_mul (x : E) :
    (j : D) * ι x = ι (σ x) * (j : D) := by
  rw [← implementingUnit_conj ι σ x, mul_assoc, Units.inv_mul, mul_one]

local notation "hj" => arithmeticImplementingUnit_mul K D E hE ι
local notation "hσ" => Eq.trans (finiteUnramifiedFrobenius_orderOf K E hE) hdegree
local notation "parameter" => cyclicParameter K D ι hj hdegree hσ

variable {π : 𝒪[K]} (hπ : Irreducible π)
variable (hInv : localBrauerInvariant K (classOf (opposite (divisionAlgebraCSA K D))) =
  reciprocalClass (CentralSimple.reducedDegree K D))

include hInv in
private theorem arithmeticParameter_order_congr :
    (d : ℤ) ∣ normalizedUnitOrder K (.ofMul (localUniformizerFieldUnit K hπ)) -
      normalizedUnitOrder K (.ofMul parameter) := by
  let e := denominatorEquiv d (CentralSimple.reducedDegree_pos K D)
  let z := normalizedUnitOrder K (.ofMul parameter)
  have hz : (z : ZMod d) = 1 := by
    apply e.injective
    apply Subtype.ext
    change (denominatorEquiv d _ (z : ZMod d) : RationalModIntegers) =
      (denominatorEquiv d _ 1 : RationalModIntegers)
    rw [denominatorEquiv_intCast, denominatorEquiv_one, ← hInv]
    exact (localBrauerInvariant_opposite_cyclicParameter K D E hE ι hdegree hj).symm
  rw [normalizedUnitOrder_localUniformizerFieldUnit]
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  change ((1 - z : ℤ) : ZMod d) = 0
  rw [Int.cast_sub, Int.cast_one, hz, sub_self]

/-- The based unramified field, its arithmetic Frobenius and the positive
reciprocal invariant determine a choice of division unit with exact power π. -/
def arithmeticDivisionUniformizer : Dˣ := by
  letI := FiniteExtension.normedField K E
  letI := FiniteExtension.valuativeRel K E
  letI := FiniteExtension.isLocalField K E
  letI := spectralFiniteExtension_valuativeExtension K E
  exact normalizeImplementingUnit K D ι hj hdegree hσ
    (spectralFiniteExtension_algebraMap_continuous K E)
    (localRamificationFactor_eq_one_of_arithmeticUnramified K E hE)
    (localUniformizerFieldUnit K hπ)
    (arithmeticParameter_order_congr K D E hE ι hdegree hπ hInv)

/-- The implementing unit has the prescribed power in the original division algebra. -/
theorem arithmeticDivisionUniformizer_pow :
    (arithmeticDivisionUniformizer K D E hE ι hdegree hπ hInv : D) ^ d =
      algebraMap K D (π : K) := by
  let := FiniteExtension.normedField K E
  let := FiniteExtension.valuativeRel K E
  let := FiniteExtension.isLocalField K E
  let := spectralFiniteExtension_valuativeExtension K E
  unfold arithmeticDivisionUniformizer
  exact normalizeImplementingUnit_pow K D ι hj hdegree hσ _ _ _ _

/-- The normalized unit still implements the same arithmetic Frobenius. -/
theorem arithmeticDivisionUniformizer_mul (x : E) :
    (arithmeticDivisionUniformizer K D E hE ι hdegree hπ hInv : D) * ι x =
      ι (σ x) * (arithmeticDivisionUniformizer K D E hE ι hdegree hπ hInv : D) := by
  let := FiniteExtension.normedField K E
  let := FiniteExtension.valuativeRel K E
  let := FiniteExtension.isLocalField K E
  let := spectralFiniteExtension_valuativeExtension K E
  unfold arithmeticDivisionUniformizer
  exact normalizeImplementingUnit_mul K D ι hj hdegree hσ _ _ _ _ x

end Langlands.ClassFieldTheory.Local
