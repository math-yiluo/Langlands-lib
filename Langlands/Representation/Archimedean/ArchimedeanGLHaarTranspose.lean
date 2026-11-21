import Langlands.Representation.Archimedean.GeneralLinear
import Langlands.Representation.Archimedean.LongestBruhatCell
import Langlands.Representation.Whittaker.BruhatHaarMeasureProof
import Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity

/-! # Haar and smoothness adapters for the archimedean transpose reduction -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped Matrix.Norms.Operator ContDiff Manifold

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.Whittaker

universe uF

variable (F : Type uF) [RCLike F] (n : ℕ)

local notation "Mat" => Matrix (Fin (n + 1)) (Fin (n + 1)) F
local notation "GL" => Langlands.GeneralLinear (n + 1) F
local notation "τ" => weylTransposeHomeomorph n F

/-- The continuous group automorphism given by Weyl-conjugated inverse transpose. -/
def weylTransposeInvMulEquiv : GL ≃ₜ* GL where
  toHomeomorph := (τ).trans (Homeomorph.inv GL)
  map_mul' x y := by
    change (τ (x * y))⁻¹ = (τ x)⁻¹ * (τ y)⁻¹
    rw [weylTransposeHomeomorph_mul, mul_inv_rev]

@[simp] theorem weylTransposeInvMulEquiv_apply (x : GL) :
    weylTransposeInvMulEquiv F n x = (τ x)⁻¹ := rfl

/-- The actual Weyl-conjugated transpose is smooth in the real matrix model. -/
theorem contMDiff_weylTransposeHomeomorph :
    ContMDiff (matrixModel F (n + 1)) (matrixModel F (n + 1)) ∞ τ := by
  apply ContMDiff.of_comp_isOpenEmbedding (Units.isOpenEmbedding_val (R := Mat))
  have he : (Units.val : GL → Mat) ∘ τ = (matrixWeylTranspose F n) ∘ (Units.val : GL → Mat) :=
    funext fun x => (matrixWeylTranspose_val F n x).symm
  rw [he]
  exact (matrixWeylTranspose F n).contDiff.contMDiff.comp Units.contMDiff_val

/-- The inverse of Weyl-conjugated transpose is likewise smooth. -/
theorem contMDiff_weylTransposeHomeomorph_symm :
    ContMDiff (matrixModel F (n + 1)) (matrixModel F (n + 1)) ∞ (τ).symm := by
  have he : ((τ).symm : GL → GL) = (τ : GL → GL) := by
    funext x
    apply (τ).injective
    rw [Homeomorph.apply_symm_apply, weylTransposeHomeomorph_involutive]
  rw [he]
  exact contMDiff_weylTransposeHomeomorph F n

section Haar

variable [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
  (μ : Measure (Langlands.GeneralLinear (n + 1) F)) [μ.IsHaarMeasure]

/-- Right invariance and the inversion and transpose symmetries of a left Haar
measure on the actual archimedean general linear group. -/
theorem archimedeanGLHaar_symmetries :
    μ.IsMulRightInvariant ∧ μ.IsInvInvariant ∧ MeasurePreserving τ μ μ ∧
      MeasurePreserving (weylTransposeInvMulEquiv F n) μ μ := by
  let : LocallyCompactSpace GL := (Units.isOpenEmbedding_val (R := Mat)).locallyCompactSpace
  let : SecondCountableTopology GL :=
    (Units.isOpenEmbedding_val (R := Mat)).isEmbedding.secondCountableTopology
  let : PseudoMetrizableSpace GL := (Units.isOpenEmbedding_val (R := Mat)).isInducing.pseudoMetrizableSpace
  have : μ.Regular := Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
  have hscalar (a : Fˣ) : Measure.modularCharacter (Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) a) = 1 := by
    change Measure.modularCharacterFun _ = 1
    rw [Measure.modularCharacterFun_eq_haarScalarFactor μ]
    have he : (fun x : GL => x * Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) a) =
        fun x : GL => Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) a * x :=
      funext fun x => (Matrix.GeneralLinearGroup.scalar_commute a x).symm
    have hm : Measure.map (fun x : GL => x * Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) a) μ = μ := by
      rw [he, map_mul_left_eq_self]
    have hSelf (ν : Measure GL) [ν.IsHaarMeasure] (hν : ν = μ) : Measure.haarScalarFactor ν μ = 1 := by
      subst ν
      exact Measure.haarScalarFactor_self μ
    exact hSelf _ hm
  have hmod (g : GL) : Measure.modularCharacterFun g = 1 :=
    RankinSelberg.GeneralLinearUnimodularity.character_eq_one Measure.modularCharacter hscalar g
  have hr : μ.IsMulRightInvariant := ⟨fun g => by
    rw [Measure.map_right_mul_eq_modularCharacterFun_smul μ g, hmod, one_smul]⟩
  have hi : μ.IsInvInvariant :=
    ⟨map_eq_self_of_antiInvolution (Homeomorph.inv GL) mul_inv_rev inv_inv μ⟩
  have hτ : MeasurePreserving τ μ μ := ⟨(τ).continuous.measurable,
    map_eq_self_of_antiInvolution τ (weylTransposeHomeomorph_mul n F)
      (weylTransposeHomeomorph_involutive n F) μ⟩
  exact ⟨hr, hi, hτ, (measurePreserving_inv μ).comp hτ⟩

end Haar

end Langlands.Archimedean
