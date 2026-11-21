import Langlands.Global.Factors.CuspidalPairEpsilonComparisonData

/-! # Archimedean factors at the standard additive scale -/

noncomputable section

set_option autoImplicit false

open scoped BigOperators Classical

namespace Langlands.BaseChange

open NumberField LocalFactor.Archimedean

universe u v w

private theorem realShifts_flatMap_length {ι : Type*} (l : List ι) (f : ι → List GammaBlock)
    (n : ℕ) (hf : ∀ i ∈ l, ((f i).flatMap GammaBlock.realShifts).length = n) :
    ((l.flatMap f).flatMap GammaBlock.realShifts).length = l.length * n := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.flatMap_cons, List.flatMap_append, List.length_append,
      hf i (by simp), ih (fun j hj => hf j (by simp [hj])), List.length_cons, Nat.add_mul, one_mul,
      add_comm]

private theorem value_gammaProduct_append (A B : List GammaBlock) (z : ℂ) :
    ((gammaProduct (A ++ B)).denominator z)⁻¹ =
      ((gammaProduct A).denominator z)⁻¹ * ((gammaProduct B).denominator z)⁻¹ := by
  simp [gammaProduct, LocalFactor.ReciprocalEntire.denominator_product, mul_comm]

private theorem value_gammaProduct_flatMap {ι : Type*} (l : List ι)
    (f : ι → List GammaBlock) (z : ℂ) :
    ((gammaProduct (l.flatMap f)).denominator z)⁻¹ =
      (l.map fun i => ((gammaProduct (f i)).denominator z)⁻¹).prod := by
  induction l with
  | nil => simp [gammaProduct, LocalFactor.ReciprocalEntire.denominator_product]
  | cons i l ih =>
    simp only [List.flatMap_cons, List.map_cons, List.prod_cons, value_gammaProduct_append, ih]

variable (F : Type u) [Field F] [NumberField F]

local notation "R" => Subtype (InfinitePlace.IsReal (K := F))
local notation "C" => Subtype (InfinitePlace.IsComplex (K := F))

/-- The Gamma blocks for the two actual standard-module parameter lists at
all infinite places, with each place included once. -/
def archimedeanPairGammaBlocks (dR dR' : R → List RealBlock)
    (dC dC' : C → List ComplexCharacterData) : List GammaBlock :=
  ((Finset.univ : Finset R).toList.flatMap fun v =>
    (realPairBlocks (dR v) (dR' v)).map RealBlock.gammaBlock) ++
  ((Finset.univ : Finset C).toList.flatMap fun v =>
    (complexPairBlocks (dC v) (dC' v)).map ComplexCharacterData.gammaBlock)

/-- The callable Gamma product is the archimedean L-product of the global pair equation. -/
theorem archimedeanPairGammaBlocks_value (dR dR' : R → List RealBlock)
    (dC dC' : C → List ComplexCharacterData) (s : ℂ) :
    ((gammaProduct (archimedeanPairGammaBlocks F dR dR' dC dC')).denominator s)⁻¹ =
      (∏ v, ((realPairLFactor (dR v) (dR' v)).denominator s)⁻¹) *
        ∏ v, ((complexPairLFactor (dC v) (dC' v)).denominator s)⁻¹ := by
  have hR (v : R) :
      gammaProduct ((realPairBlocks (dR v) (dR' v)).map RealBlock.gammaBlock) =
        realPairLFactor (dR v) (dR' v) := by
    simp [gammaProduct, realPairLFactor, realLFactor, Function.comp_def, RealBlock.gammaBlock_factor]
  have hC (v : C) :
      gammaProduct ((complexPairBlocks (dC v) (dC' v)).map ComplexCharacterData.gammaBlock) =
        complexPairLFactor (dC v) (dC' v) := by
    simp [gammaProduct, complexPairLFactor, complexLFactor, Function.comp_def,
      ComplexCharacterData.gammaBlock_factor]
  simp only [archimedeanPairGammaBlocks, value_gammaProduct_append, value_gammaProduct_flatMap, hR, hC,
    Finset.prod_map_toList]

/-- Each real place contributes the pair rank, each complex place twice the
pair rank. The total count is the pair rank times the absolute field degree. -/
theorem archimedeanPairGammaBlocks_count (dR dR' : R → List RealBlock)
    (dC dC' : C → List ComplexCharacterData) (n : ℕ)
    (hR : ∀ v, realRank (dR v) * realRank (dR' v) = n)
    (hC : ∀ v, (dC v).length * (dC' v).length = n) :
    ((archimedeanPairGammaBlocks F dR dR' dC dC').flatMap GammaBlock.realShifts).length =
      Module.finrank ℚ F * n := by
  have hr (v : R) : (((realPairBlocks (dR v) (dR' v)).map RealBlock.gammaBlock).flatMap
      GammaBlock.realShifts).length = n := (realPairGammaCount _ _).trans (hR v)
  have hc (v : C) : (((complexPairBlocks (dC v) (dC' v)).map ComplexCharacterData.gammaBlock).flatMap
      GammaBlock.realShifts).length = 2 * n := by rw [complexPairGammaCount, hC v]
  rw [archimedeanPairGammaBlocks, List.flatMap_append, List.length_append,
    realShifts_flatMap_length _ _ _ (fun i _ => hr i),
    realShifts_flatMap_length _ _ _ (fun i _ => hc i)]
  simp only [Finset.length_toList, Finset.card_univ]
  rw [← InfinitePlace.card_add_two_mul_card_eq_rank F]
  change Fintype.card R * n + Fintype.card C * (2 * n) =
    (Fintype.card R + 2 * Fintype.card C) * n
  ring

/-- At standard additive scale the actual infinite pair epsilon product is
constant, with value a complex unit determined by the chosen parameters. -/
theorem archimedeanPairEpsilon_standard_value (dR dR' : R → List RealBlock)
    (dC dC' : C → List ComplexCharacterData) (s : ℂ) :
    ((∏ v, realPairEpsilon (dR v) (dR' v) 1 (NNReal.sqrt ‖((1 : ℝˣ) : ℝ)‖₊)
      (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr (1 : ℝˣ).ne_zero)) s) *
      ∏ v, complexPairEpsilon (dC v) (dC' v) 1 ‖((1 : ℂˣ) : ℂ)‖₊
        (nnnorm_pos.mpr (1 : ℂˣ).ne_zero) s) =
      (∏ v, realPairStandardEpsilon (dR v) (dR' v)) *
        ∏ v, complexPairStandardEpsilon (dC v) (dC' v) := by
  simp [realPairEpsilon, complexPairEpsilon, realPairStandardEpsilon, complexPairStandardEpsilon,
    realEpsilon_standard, complexEpsilon_standard]

/-- For a family indexed by as many characters as the relative degree, the
real Gamma count of the product of base equations matches the upper count
whenever each degree-normalized count is the common pair rank. -/
def ArchimedeanPairGammaCountComparisonStatement : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (I : Type w) (X : Finset I), X.card = Module.finrank K L →
    ∀ (n : ℕ) (A : I → List GammaBlock) (B : List GammaBlock),
      (∀ i ∈ X, ((A i).flatMap GammaBlock.realShifts).length = Module.finrank ℚ K * n) →
      (B.flatMap GammaBlock.realShifts).length = Module.finrank ℚ L * n →
      ((X.toList.flatMap A).flatMap GammaBlock.realShifts).length =
        (B.flatMap GammaBlock.realShifts).length

theorem archimedeanPairGammaCountComparison : ArchimedeanPairGammaCountComparisonStatement.{u, v, w} := by
  intro K L _ _ _ _ _ I X hX n A B hA hB
  rw [realShifts_flatMap_length X.toList A _ (fun i hi => hA i (Finset.mem_toList.mp hi)),
    Finset.length_toList, hX, hB, ← Module.finrank_mul_finrank ℚ K L]
  ring

end Langlands.BaseChange
