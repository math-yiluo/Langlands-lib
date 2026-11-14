import Langlands.Representation.Induction.SingleBlock
import Langlands.AllField.Representation.Induction.BlockFactors
import Langlands.AllField.Representation.Induction.SingleBlock
/-! Evaluation equivalences for single-block normalized induction. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllField.Induction
open Langlands.Induction
open Langlands.AllField.Induction

universe uR uG uV


end Langlands.AllField.Induction

namespace Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape
open Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

universe uF uV


end Langlands.AllField.GeneralLinear.BlockShape

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

universe uF uV

variable {F : Type uF} [Field F]
variable (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)
variable (hB : B.length = 1)

include hB

@[simp] theorem singleBlock_parabolicHalfModulus (g : B.parabolic F) :
    T.parabolicHalfModulus B g = 1 :=
  T.singleBlock_leviHalfModulus B hB _

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Evaluation at the identity identifies normalized induction from a single block
with the original Levi action transported to the ambient general linear group. -/
def singleBlockNormalizedInducedEquiv (σ : Representation ℂ (B.Levi F) V)
    (hσ : letI := T.leviTopology B; IsSmooth σ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedParabolicInduced B σ).Equiv
      (σ.comp (B.singleBlockLeviEquiv hB F).symm.toMonoidHom) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  let e := B.singleBlockLeviEquivContinuous hB F
  exact Induction.smoothInducedTopEquiv (B.parabolic F)
    (B.singleBlock_parabolic_eq_top hB F)
    (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F)))
    (σ.comp (B.singleBlockLeviEquiv hB F).symm.toMonoidHom)
    (by
      intro g
      ext v
      change (T.parabolicHalfModulus B g : ℂ) •
        σ (B.leviProjection F g) v = _
      rw [T.singleBlock_parabolicHalfModulus B hB]
      simp only [Units.val_one, one_smul]
      rfl)
    (isSmooth_comp e.symm.toMonoidHom e.symm.continuous hσ)

variable (σ : Representation ℂ (B.Levi F) V)
variable (hσ : letI := T.leviTopology B; IsSmooth σ)

@[simp]
theorem singleBlockNormalizedInducedEquiv_apply
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.parabolic F)
        (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F)))) :
    T.singleBlockNormalizedInducedEquiv B hB σ hσ f = f.1.1 1 := rfl

@[simp]
theorem singleBlockNormalizedInducedEquiv_symm_eval (v : V)
    (g : GeneralLinear n F) :
    (T.singleBlockNormalizedInducedEquiv B hB σ hσ).symm v |>.1.1 g =
      σ ((B.singleBlockLeviEquiv hB F).symm g) v := rfl

section Product

variable {W : Fin B.length → Type uV}
variable [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- A one-block normalized product is its unique factor, after the explicit rank transport. -/
def singleBlockNormalizedProductEquiv
    (τ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (W i))
    (hτ : letI := T.topology; ∀ i, IsSmooth (τ i)) (i : Fin B.length) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedProductInduced B τ).Equiv
      ((τ i).comp
        (GeneralLinear.reindex (R := F) (finCongr (B.singleBlock_size hB i))).symm.toMonoidHom) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  let e := B.singleBlockTensorEquiv hB τ i
  refine (T.singleBlockNormalizedInducedEquiv B hB (B.blockTensor τ)
    (FiniteTensor.isSmooth_external τ hτ)).trans
    (Representation.Equiv.mk e.toLinearEquiv ?_)
  intro g
  apply LinearMap.ext
  intro v
  have hh := DFunLike.congr_fun
    (e.isIntertwining' ((B.singleBlockLeviEquiv hB F).symm g)) v
  change e ((B.blockTensor τ) ((B.singleBlockLeviEquiv hB F).symm g) v) =
    τ i ((B.singleBlockLeviEquiv hB F).symm g i) (e v) at hh
  rw [B.singleBlockLeviEquiv_symm_coordinate hB g i] at hh
  exact hh

/-- Product evaluation is evaluation at one followed by the existing singleton tensor map. -/
@[simp] theorem singleBlockNormalizedProductEquiv_apply
    (τ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (W i))
    (hτ : letI := T.topology; ∀ i, IsSmooth (τ i)) (i : Fin B.length)
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.parabolic F)
        (twist (T.parabolicHalfModulus B) ((B.blockTensor τ).comp (B.leviProjection F)))) :
    letI := T.topology
    T.singleBlockNormalizedProductEquiv B hB τ hτ i f =
      B.singleBlockTensorEquiv hB τ i (f.1.1 1) := rfl

end Product

end Langlands.LocalFieldData
