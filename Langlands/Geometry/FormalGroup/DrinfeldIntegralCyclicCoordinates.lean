import Langlands.Geometry.FormalGroup.DrinfeldArithmeticIntegers
import Langlands.Algebra.ReducedNormSubfield

/-! # Integral cyclic coordinates of the actual division order -/

noncomputable section

namespace Langlands.FormalGroup.LocalDivision

open ValuativeRel CentralDivision CentralSimple Langlands.ClassFieldTheory.Local
open Langlands.LocalField Langlands.LocalGalois Langlands.LocalGalois.Separable
open scoped TensorProduct WithZero

universe u

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

local instance integralCyclicBaseNormedField : NontriviallyNormedField K := localNormedField K
local instance integralCyclicBaseUltrametric : IsUltrametricDist K := localNormedField_ultrametric K
local instance integralCyclicBaseComplete : CompleteSpace K := localNormedField_complete K

variable (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E] [IsGalois K E]
  (hE : ArithmeticUnramified K E) (ι : E →ₐ[K] D)
  (hdegree : Module.finrank K E = CentralSimple.reducedDegree K D)

local instance integralCyclicNormedField : NontriviallyNormedField E := FiniteExtension.normedField K E
local instance integralCyclicValuativeRel : ValuativeRel E := FiniteExtension.valuativeRel K E
local instance integralCyclicLocalField : IsNonarchimedeanLocalField E := FiniteExtension.isLocalField K E
local instance integralCyclicValuativeExtension : ValuativeExtension K E :=
  spectralFiniteExtension_valuativeExtension K E

local notation "d" => CentralSimple.reducedDegree K D
local notation "vD" => localReducedNormIntValuation K D
local notation "orderE" => normalizedUnitOrder E

include hdegree hE in
omit [IsGalois K E] in
private theorem embeddedUnit_value (a : Eˣ) :
    vD (ι (a : E)) = WithZero.exp (-((d : ℤ) * orderE (.ofMul a))) := by
  have hn := normalizedUnitOrder_norm_of_unramified K E
    (spectralFiniteExtension_algebraMap_continuous K E)
    (localRamificationFactor_eq_one_of_arithmeticUnramified K E hE) a
  rw [hdegree] at hn
  rw [localReducedNormIntValuation_apply, reducedNorm_eq_field_norm K D ι hdegree]
  change discreteLocalValuation K (Algebra.norm K (a : E)) = _
  exact (discreteLocalValuation_of_unit K (Langlands.LocalClassField.normUnits K E a)).trans
    (congrArg (fun z : ℤ => WithZero.exp (-z)) hn)

omit [IsGalois K E] in
private theorem embeddedUnit_integral_iff (a : Eˣ) :
    localDivisionSubfieldValuation K D ι (a : E) ≤ 1 ↔ 0 ≤ orderE (.ofMul a) := by
  let : (spectralValuation K E).Compatible := Valuation.Compatible.ofValuation _
  rw [normalizedUnitOrder_nonneg_iff, Valuation.vle_iff_le (spectralValuation K E)]
  have h := (subfieldSpectralValuation_le_iff K D E ι (a : E) 1).symm
  simpa only [map_one] using h

variable {π : 𝒪[K]} (hπ : Irreducible π) {j : Dˣ}
  (hpower : (j : D) ^ CentralSimple.reducedDegree K D = algebraMap K D (π : K))

include hπ hpower in
private theorem implementingUniformizer_value : vD (j : D) = WithZero.exp (-1 : ℤ) := by
  have h := discreteLocalValuation_of_unit K (localUniformizerFieldUnit K hπ)
  rw [normalizedUnitOrder_localUniformizerFieldUnit] at h
  apply (pow_left_inj₀ zero_le zero_le (reducedDegree_pos K D).ne').mp
  rw [← map_pow, hpower, localReducedNormIntValuation_algebraMap]
  exact congrArg (fun t : ℤᵐ⁰ => t ^ d) h

include hE hdegree hπ hpower in
omit [IsGalois K E] in
private theorem cyclicTerm_value (a : Eˣ) (i : Fin d) :
    vD (ι (a : E) * (j : D) ^ i.val) =
      WithZero.exp (-((d : ℤ) * orderE (.ofMul a) + (i.val : ℤ))) := by
  rw [map_mul, map_pow, embeddedUnit_value K D E hE ι hdegree,
    implementingUniformizer_value K D hπ hpower, ← WithZero.exp_nsmul, ← WithZero.exp_add]
  congr 1
  simp only [nsmul_eq_mul, mul_neg, mul_one, neg_add_rev, add_comm]

include hE hdegree hπ hpower in
omit [IsGalois K E] in
private theorem cyclicTerm_integral_iff (a : E) (i : Fin d) :
    vD (ι a * (j : D) ^ i.val) ≤ 1 ↔ localDivisionSubfieldValuation K D ι a ≤ 1 := by
  by_cases ha : a = 0
  · simp [ha]
  let t : Eˣ := Units.mk0 a ha
  change vD (ι (t : E) * (j : D) ^ i.val) ≤ 1 ↔ localDivisionSubfieldValuation K D ι (t : E) ≤ 1
  rw [cyclicTerm_value K D E hE ι hdegree hπ hpower, WithZero.exp_le_one_iff,
    embeddedUnit_integral_iff K D E ι]
  have hi : (i.val : ℤ) < (d : ℤ) := by exact_mod_cast i.isLt
  have hd : (0 : ℤ) ≤ (d : ℤ) := by positivity
  constructor
  · intro h
    by_contra hneg
    have hle : orderE (.ofMul t) ≤ -1 := by omega
    have hmul := mul_le_mul_of_nonneg_left hle hd
    rw [mul_neg_one] at hmul
    omega
  · intro h
    have hmul := mul_nonneg hd h
    omega

include hE hdegree hπ hpower in
omit [IsGalois K E] in
private theorem cyclicTerm_value_ne (a b : Eˣ) {i k : Fin d} (hik : i ≠ k) :
    vD (ι (a : E) * (j : D) ^ i.val) ≠ vD (ι (b : E) * (j : D) ^ k.val) := by
  rw [cyclicTerm_value K D E hE ι hdegree hπ hpower,
    cyclicTerm_value K D E hE ι hdegree hπ hpower]
  intro h
  have hsum := neg_injective (WithZero.exp_injective h)
  have hrem (z : ℤ) (r : Fin d) : ((d : ℤ) * z + (r.val : ℤ)) % (d : ℤ) = (r.val : ℤ) := by
    rw [Int.add_emod, Int.mul_emod_right, zero_add, Int.emod_emod,
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast r.isLt)]
  have hmod := congrArg (fun z : ℤ => z % (d : ℤ)) hsum
  rw [hrem, hrem] at hmod
  exact hik (Fin.ext (by exact_mod_cast hmod))

include hE hdegree hπ hpower in
omit [IsGalois K E] in
private theorem cyclicSum_integral_iff (a : Fin d → E) :
    vD (∑ i, ι (a i) * (j : D) ^ i.val) ≤ 1 ↔
      ∀ i, localDivisionSubfieldValuation K D ι (a i) ≤ 1 := by
  let f := fun i : Fin d => ι (a i) * (j : D) ^ i.val
  change vD (∑ i, f i) ≤ 1 ↔ _
  constructor
  · intro hs i
    apply (cyclicTerm_integral_iff K D E hE ι hdegree hπ hpower (a i) i).mp
    change vD (f i) ≤ 1
    by_contra! hbad
    obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ (fun r => vD (f r))
      ⟨i, Finset.mem_univ i⟩
    have hk₁ : 1 < vD (f k) := hbad.trans_le (hk i (Finset.mem_univ i))
    have hzero (r : Fin d) (h : a r = 0) : vD (f r) = 0 := by simp [f, h]
    have hk₀ : a k ≠ 0 := fun h => by rw [hzero k h] at hk₁; exact (not_lt_of_ge zero_le) hk₁
    have heq : vD (∑ r, f r) = vD (f k) := by
      apply Valuation.map_sum_eq_of_lt vD (Finset.mem_univ k)
      intro r hr
      have hrk : r ≠ k := by simpa using (Finset.mem_sdiff.mp hr).2
      by_cases hr₀ : a r = 0
      · rw [hzero r hr₀]
        exact zero_lt_one.trans hk₁
      · apply lt_of_le_of_ne (hk r (Finset.mem_univ r))
        exact cyclicTerm_value_ne K D E hE ι hdegree hπ hpower
          (Units.mk0 (a r) hr₀) (Units.mk0 (a k) hk₀) hrk
    exact (not_lt_of_ge (heq ▸ hs)) hk₁
  · intro ha
    exact Valuation.map_sum_le vD (fun i _ =>
      (cyclicTerm_integral_iff K D E hE ι hdegree hπ hpower (a i) i).mpr (ha i))

variable {σ : E ≃ₐ[K] E}
  (horder : orderOf σ = CentralSimple.reducedDegree K D)
  (hconj : ∀ a : E, (j : D) * ι a = ι (σ a) * (j : D))

include hE hdegree hπ hpower horder hconj in
private theorem cyclicBasis_integral_iff (x : D) :
    letI := localDivisionSubfieldLeftModule K D ι
    localReducedNormValuation K D x ≤ 1 ↔
      ∀ i, localDivisionSubfieldValuation K D ι
        ((implementingUnitBasis K D ι hconj hdegree horder).repr x i) ≤ 1 := by
  let := localDivisionSubfieldLeftModule K D ι
  let b := implementingUnitBasis K D ι hconj hdegree horder
  let a := fun i => b.repr x i
  have hs : (∑ i, ι (a i) * (j : D) ^ i.val) = x := by
    conv_rhs => rw [← b.sum_repr x]
    apply Finset.sum_congr rfl
    intro i _
    change ι (a i) * (j : D) ^ i.val = ι (a i) * b i
    rw [show b i = (j : D) ^ i.val from implementingUnitBasis_apply K D ι hconj hdegree horder i]
  have h := cyclicSum_integral_iff K D E hE ι hdegree hπ hpower a
  rw [hs] at h
  have hval := localReducedNormIntValuation_le_iff K D x 1
  rw [map_one, map_one] at hval
  exact hval.symm.trans h

/-- The actual division order has integral coefficients in the cyclic basis
of a normalized division uniformizer. -/
def integerCyclicCoordinates : IntegerRing K D ≃ (Fin d → SubfieldIntegerRing K D ι) := by
  letI := localDivisionSubfieldLeftModule K D ι
  let b := (implementingUnitBasis K D ι hconj hdegree horder).equivFun
  have hb (x : D) : localReducedNormValuation K D x ≤ 1 ↔
      ∀ i, localDivisionSubfieldValuation K D ι (b x i) ≤ 1 :=
    cyclicBasis_integral_iff K D E hE ι hdegree hπ hpower horder hconj x
  let coeff := fun a : Fin d → SubfieldIntegerRing K D ι => fun i => (a i : E)
  exact
    { toFun := fun x i => ⟨b (x : D) i, (hb x).mp x.property i⟩
      invFun := fun a => ⟨b.symm (coeff a), (hb _).mpr (fun i => by
        rw [b.apply_symm_apply]
        exact (a i).property)⟩
      left_inv := fun x => Subtype.ext (b.symm_apply_apply x.val)
      right_inv := fun a => funext fun i => Subtype.ext (congrFun (b.apply_symm_apply (coeff a)) i) }

end Langlands.FormalGroup.LocalDivision
