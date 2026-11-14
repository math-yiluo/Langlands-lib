import Langlands.AllFieldBZ.Group.GL.Maps
import Langlands.AllFieldBZ.Representation.Induction.BlockFactors
import Langlands.Representation.Induction.SingleBlock

/-!
# All-field port of `Langlands.Representation.Induction.SingleBlock`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Induction.SingleBlock` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllFieldBZ.Induction
open Langlands.Induction
universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V]

end Langlands.AllFieldBZ.Induction
namespace Langlands.AllFieldBZ.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape
universe uF uV

variable {R : Type uF} [CommRing R] {n : ℕ} (B : Langlands.GeneralLinear.BlockShape n) (hB : B.length = 1)

end Langlands.AllFieldBZ.GeneralLinear.BlockShape
namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
universe uF uV

variable {F : LocalFieldPackage.{uF}}
variable (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
variable (hB : B.length = 1)

include hB

/-- The explicit single-block modulus is an empty product of block-pair factors. -/
@[simp] theorem singleBlock_leviModulus (m : B.Levi F.Carrier) :
    T.leviModulus B m = 1 := by
  rw [T.leviModulus_apply]
  apply Finset.prod_eq_one
  intro i _
  apply Finset.prod_eq_one
  intro j hj
  have hij := (Finset.mem_filter.mp hj).2
  have he : i = j := (B.eq_singleBlockIndex hB i).trans
    (B.eq_singleBlockIndex hB j).symm
  exact False.elim ((ne_of_lt hij) he)

@[simp] theorem singleBlock_parabolicModulus (g : B.parabolic F.Carrier) :
    T.parabolicModulus B g = 1 :=
  T.singleBlock_leviModulus B hB _

@[simp] theorem singleBlock_leviHalfModulus (m : B.Levi F.Carrier) :
    T.leviHalfModulus B m = 1 :=
  (T.leviHalfModulus_eq_one B m).mpr (T.singleBlock_leviModulus B hB m)

@[simp] theorem singleBlock_parabolicHalfModulus (g : B.parabolic F.Carrier) :
    T.parabolicHalfModulus B g = 1 :=
  T.singleBlock_leviHalfModulus B hB _

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Evaluation at the identity identifies normalized induction from a single block
with the original Levi action transported to the ambient general linear group. -/
def singleBlockNormalizedInducedEquiv (σ : Representation ℂ (B.Levi F.Carrier) V)
    (hσ : letI := T.leviTopology B; IsSmooth σ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedParabolicInduced B σ).Equiv
      (σ.comp (B.singleBlockLeviEquiv hB F.Carrier).symm.toMonoidHom) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  let e := B.singleBlockLeviEquivContinuous hB F.Carrier
  exact Induction.smoothInducedTopEquiv (B.parabolic F.Carrier)
    (B.singleBlock_parabolic_eq_top hB F.Carrier)
    (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier)))
    (σ.comp (B.singleBlockLeviEquiv hB F.Carrier).symm.toMonoidHom)
    (by
      intro g
      ext v
      change (T.parabolicHalfModulus B g : ℂ) •
        σ (B.leviProjection F.Carrier g) v = _
      rw [T.singleBlock_parabolicHalfModulus B hB]
      simp only [Units.val_one, one_smul]
      rfl)
    (isSmooth_comp e.symm.toMonoidHom e.symm.continuous hσ)

variable (σ : Representation ℂ (B.Levi F.Carrier) V)
variable (hσ : letI := T.leviTopology B; IsSmooth σ)

@[simp]
theorem singleBlockNormalizedInducedEquiv_apply
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier)))) :
    T.singleBlockNormalizedInducedEquiv B hB σ hσ f = f.1.1 1 := rfl

@[simp]
theorem singleBlockNormalizedInducedEquiv_symm_eval (v : V)
    (g : GeneralLinear n F.Carrier) :
    (T.singleBlockNormalizedInducedEquiv B hB σ hσ).symm v |>.1.1 g =
      σ ((B.singleBlockLeviEquiv hB F.Carrier).symm g) v := rfl

section Product
variable {W : Fin B.length → Type uV}
variable [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- A one-block normalized product is its unique factor, after the explicit rank transport. -/
def singleBlockNormalizedProductEquiv
    (τ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (W i))
    (hτ : letI := T.topology; ∀ i, IsSmooth (τ i)) (i : Fin B.length) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedProductInduced B τ).Equiv
      ((τ i).comp
        (GeneralLinear.reindex (R := F.Carrier) (finCongr (B.singleBlock_size hB i))).symm.toMonoidHom) := by
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
    (e.isIntertwining' ((B.singleBlockLeviEquiv hB F.Carrier).symm g)) v
  change e ((B.blockTensor τ) ((B.singleBlockLeviEquiv hB F.Carrier).symm g) v) =
    τ i ((B.singleBlockLeviEquiv hB F.Carrier).symm g i) (e v) at hh
  rw [B.singleBlockLeviEquiv_symm_coordinate hB g i] at hh
  exact hh

/-- Product evaluation is evaluation at one followed by the existing singleton tensor map. -/
@[simp] theorem singleBlockNormalizedProductEquiv_apply
    (τ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (W i))
    (hτ : letI := T.topology; ∀ i, IsSmooth (τ i)) (i : Fin B.length)
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B) ((B.blockTensor τ).comp (B.leviProjection F.Carrier)))) :
    letI := T.topology
    T.singleBlockNormalizedProductEquiv B hB τ hτ i f =
      B.singleBlockTensorEquiv hB τ i (f.1.1 1) := rfl

end Product
end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
