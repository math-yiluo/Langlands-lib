import Langlands.Global.RankinSelberg.RealWhittakerEvaluation
import Langlands.Representation.Archimedean.RealJacquetFiniteGenerationProof
import Langlands.Representation.Archimedean.RealStandardModuleAdmissible
import Langlands.Representation.Archimedean.RealTemperedIrreducibleProof
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Uniform growth of real coefficients from finite generation -/

noncomputable section

open scoped TensorProduct
open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open Langlands.Archimedean.RealJacquetFiniteGeneration (op wordOp wordSpan)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealUniformWhittaker

variable {r : ℕ} {ds : List RealBlock} {a : ℝˣ}
local notation "V" => Automorphic.realStandardKFinite (r + 1) ds
local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "π" => realStandardLie (r + 1) ds

private def growthBoundSubmodule (N : ℕ) : Submodule ℂ (G → ℂ) where
  carrier := {W | ∃ C : ℝ, 0 ≤ C ∧ ∀ g, ‖W g‖ ≤ C * realMatrixHeight g ^ N}
  zero_mem' := ⟨0, le_rfl, by simp⟩
  add_mem' := by
    rintro W W' ⟨C, hC, hW⟩ ⟨D, hD, hW'⟩
    refine ⟨C + D, add_nonneg hC hD, fun g => ?_⟩
    change ‖W g + W' g‖ ≤ _
    rw [add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hW g) (hW' g))
  smul_mem' := by
    rintro z W ⟨C, hC, hW⟩
    refine ⟨‖z‖ * C, mul_nonneg (norm_nonneg _) hC, fun g => ?_⟩
    change ‖z * W g‖ ≤ _
    rw [norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hW g) (norm_nonneg _)

private theorem coefficient_wordOp {B : V →ₗ[ℂ] (G → ℂ)}
    (hB : IsRealWhittakerIntertwiner r ds a B) (w : List (Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ))
    (v : V) : B (wordOp π w v) = RealLocalWhittaker.iteratedRightDerivative r w (B v) := by
  induction w with
  | nil => rfl
  | cons X w ih =>
    rw [RealJacquetFiniteGeneration.wordOp_cons, Module.End.mul_apply, op]
    rw [hB.2.2.2.2 X (wordOp π w v) _
      (realStandardLie_one_tmul_apply_coe (r + 1) ds X (wordOp π w v)), ih]
    rfl

/-- Finitely many generators under matrix right-derivative words suffice to make the
growth exponent of a coefficient map independent of the source vector. -/
theorem intertwiner_of_wordSpan_eq_top {B : V →ₗ[ℂ] (G → ℂ)}
    (hB : IsRealWhittakerIntertwiner r ds a B)
    (F : Submodule ℂ V) [FiniteDimensional ℂ F] (hF : wordSpan π F = ⊤) :
    IsRealUniformWhittakerIntertwiner r ds a B := by
  classical
  let _ : Module.Free ℂ F := Module.Free.of_divisionRing ℂ F
  let b : Module.Basis (Fin (Module.finrank ℂ F)) ℂ F := Module.finBasis ℂ F
  choose d hd using fun i => RealWhittakerEvaluation.coefficients_uniformDerivativeGrowth
    ℚ r ds ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩ hB (b i : V)
  let N := Finset.univ.sup d
  let S := (growthBoundSubmodule (r := r) N).comap B
  have hspan : wordSpan π F ≤ S := by
    apply RealJacquetFiniteGeneration.wordSpan_le
    intro w f hf
    have hBasis (i : Fin (Module.finrank ℂ F)) : wordOp π w (b i : V) ∈ S := by
      obtain ⟨C, hC, h⟩ := hd i w
      refine ⟨C, hC, fun g => ?_⟩
      rw [coefficient_wordOp hB]
      exact (h g).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀
        ((by norm_num : (1 : ℝ) ≤ 2).trans
          (RealPlaceRestriction.two_le_realMatrixHeight (Nat.succ_pos r) g))
        (Finset.le_sup (Finset.mem_univ i))) hC)
    let f' : F := ⟨f, hf⟩
    have hf' : f = ∑ i, b.repr f' i • (b i : V) := by
      simpa only [f', map_sum, map_smul, Submodule.subtype_apply] using
        congrArg F.subtype (b.sum_repr f').symm
    rw [hf', map_sum]
    exact Submodule.sum_mem S fun i _ => by rw [map_smul]; exact S.smul_mem _ (hBasis i)
  exact ⟨hB, N, fun f => hspan (hF.symm ▸ Submodule.mem_top)⟩

theorem model_le_uniform_of_wordSpan_eq_top (F : Submodule ℂ V) [FiniteDimensional ℂ F]
    (hF : wordSpan π F = ⊤) : realWhittakerModel r ds a ≤ realUniformWhittakerModel r ds a := by
  refine iSup_le fun B => iSup_le fun hB => ?_
  exact le_iSup_of_le B (le_iSup_of_le (intertwiner_of_wordSpan_eq_top hB F hF) le_rfl)

theorem models_eq_of_irreducible
    (hI : IsIrreducibleGKModule (realStandardRep (r + 1) ds) π) :
    realWhittakerModel r ds a = realUniformWhittakerModel r ds a := by
  obtain ⟨F, hdim, hF⟩ := RealJacquetFiniteGeneration.realJacquetFiniteGeneration (r + 1)
    V (realStandardRep (r + 1) ds) π
    (isRealGKModule_realStandardModule (r + 1) ds) hI (realStandardAdmissible (r + 1) ds)
  let _ : FiniteDimensional ℂ F := hdim
  refine le_antisymm (model_le_uniform_of_wordSpan_eq_top F (hF _ ?_ ?_)) (model_le_model ds a)
  · intro f hf
    have hf' : wordOp π [] f ∈ wordSpan π F :=
      RealJacquetFiniteGeneration.wordOp_apply_mem_wordSpan [] hf
    simpa using hf'
  · intro X _ v hv
    change op π X v ∈ wordSpan π F
    exact RealJacquetFiniteGeneration.op_apply_mem_wordSpan X hv

end RealUniformWhittaker

/-- The exact and uniform Whittaker coefficient spaces agree for a real standard module
whose real block exponents all coincide. -/
def RealTiedWhittakerModelUniformityStatement : Prop :=
  ∀ (r : ℕ) (ds : List RealBlock), realRank ds = r + 1 →
    (∀ x ∈ ds, ∀ y ∈ ds, realBlockExponent x = realBlockExponent y) →
    ∀ a : ℝˣ, realWhittakerModel r ds a = realUniformWhittakerModel r ds a

theorem realTiedWhittakerModelUniformity : RealTiedWhittakerModelUniformityStatement :=
  fun r ds hRank hExp _ => RealUniformWhittaker.models_eq_of_irreducible
    (realTemperedStandardIrreducible (r + 1) ds hRank hExp)

end Langlands.Global.RankinSelbergGlobal
