import Langlands.Representation.Induction.SingleBlock
import Langlands.AllField.Group.GL.BlockModulus
/-! Evaluation equivalences for single-block normalized induction. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllField.Induction
open Langlands.Induction
open Langlands.AllField.Induction

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V]

end Langlands.AllField.Induction

namespace Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape
open Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

universe uF uV

variable {R : Type uF} [CommRing R] {n : ℕ} (B : BlockShape n) (hB : B.length = 1)

end Langlands.AllField.GeneralLinear.BlockShape

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

universe uF uV

variable {F : Type uF} [Field F]
variable (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)
variable (hB : B.length = 1)

include hB

/-- The explicit single-block modulus is an empty product of block-pair factors. -/
@[simp] theorem singleBlock_leviModulus (m : B.Levi F) :
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

@[simp] theorem singleBlock_leviHalfModulus (m : B.Levi F) :
    T.leviHalfModulus B m = 1 :=
  (T.leviHalfModulus_eq_one B m).mpr (T.singleBlock_leviModulus B hB m)

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

variable (σ : Representation ℂ (B.Levi F) V)
variable (hσ : letI := T.leviTopology B; IsSmooth σ)

section Product

variable {W : Fin B.length → Type uV}
variable [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

end Product

end Langlands.LocalFieldData
