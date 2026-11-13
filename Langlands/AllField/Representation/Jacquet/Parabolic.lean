import Langlands.Representation.Jacquet.Parabolic
import Langlands.AllField.Group.GL.BlockModulus
/-!
# Normalized Jacquet modules for standard block parabolics

The Jacquet module of a representation of `GL_n` along a standard block parabolic
is the actual coinvariant quotient of its restriction to the parabolic by the
unipotent radical. The Levi acts through its section into the parabolic,
normalized by the inverse square root of a supplied full positive modulus. For
nonarchimedean local fields that modulus is the explicit block modulus.
-/

noncomputable section

open CategoryTheory
open scoped NNReal

namespace Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape
open Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

universe uF uV uW uX

variable {F : Type uF} [CommRing F] {n : ℕ} (B : BlockShape n)
variable {V : Type uV} {W : Type uW} {X : Type uX}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable [AddCommGroup X] [Module ℂ X]

section Topology

variable [TopologicalSpace F] [IsTopologicalRing F]

end Topology

end Langlands.AllField.GeneralLinear.BlockShape

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

universe uF uV uW

variable {F : Type uF} [Field F]
variable (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

private theorem isTopologicalRing :
    letI := T.topology
    IsTopologicalRing F := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

/-- The normalized Jacquet module `r_P(ρ)` of an actual nonarchimedean local field, using the
full explicit block modulus `T.leviModulus B`. -/
def normalizedJacquet (ρ : Representation ℂ (GeneralLinear n F) V) :
    Representation ℂ (B.Levi F) (B.JacquetModule ρ) :=
  B.normalizedJacquetOf (T.leviModulus B) ρ

/-- The Levi acts by `δ_P(m)^(-1/2)` times the action of the embedded block
diagonal matrix. -/
theorem normalizedJacquet_mk (ρ : Representation ℂ (GeneralLinear n F) V)
    (m : B.Levi F) (v : V) :
    T.normalizedJacquet B ρ m (B.jacquetMk ρ v) =
      (((NNReal.sqrt (T.leviModulus B m : ℝ≥0) : ℝ) : ℂ))⁻¹ •
        B.jacquetMk ρ (ρ (B.leviEmbedding F m) v) :=
  B.normalizedJacquetOf_mk _ ρ m v

/-- The normalizing scalar is the inverse of the induction half. -/
theorem normalizedJacquet_mk_eq_inv_halfModulus
    (ρ : Representation ℂ (GeneralLinear n F) V)
    (m : B.Levi F) (v : V) :
    T.normalizedJacquet B ρ m (B.jacquetMk ρ v) =
      ((T.leviHalfModulus B m)⁻¹ : ℂˣ) •
        B.jacquetMk ρ (ρ (B.leviEmbedding F m) v) := by
  rw [normalizedJacquet_mk, Units.smul_def, Units.val_inv_eq_inv_val,
    leviHalfModulus_apply]

theorem isSmooth_normalizedJacquet
    {ρ : Representation ℂ (GeneralLinear n F) V} :
    letI := T.topology
    IsSmooth ρ → IsSmooth (T.normalizedJacquet B ρ) := by
  let := T.topology
  let := T.isTopologicalRing
  exact B.isSmooth_normalizedJacquetOf (T.leviModulus B) (T.isOpen_ker_leviModulus B)

/-- The normalized Jacquet functor of canonical smooth categories. -/
def normalizedJacquetFunctor :
    letI := T.generalLinearTopology n
    letI := T.leviTopology B
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F) ⥤
      SmoothRep.{0, uF, uV} ℂ (B.Levi F) :=
  letI := T.topology
  letI := T.isTopologicalRing
  B.normalizedJacquetFunctorOf (T.leviModulus B) (T.isOpen_ker_leviModulus B)

end Langlands.LocalFieldData

namespace Langlands

universe uF uV

variable (F : Type uF) [Field F]
variable {n : ℕ} (B : GeneralLinear.BlockShape n)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

end Langlands
