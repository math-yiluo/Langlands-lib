import Langlands.AllFieldBZ.Group.GL.BlockModulus
import Langlands.Representation.Jacquet.Parabolic

/-!
# All-field port of `Langlands.Representation.Jacquet.Parabolic`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Jacquet.Parabolic` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
open scoped NNReal
namespace Langlands.AllFieldBZ.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape
universe uF uV uW uX

variable {F : Type uF} [CommRing F] {n : ℕ} (B : Langlands.GeneralLinear.BlockShape n)
variable {V : Type uV} {W : Type uW} {X : Type uX}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable [AddCommGroup X] [Module ℂ X]

section Topology
variable [TopologicalSpace F] [IsTopologicalRing F]

end Topology
end Langlands.AllFieldBZ.GeneralLinear.BlockShape
namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
universe uF uV uW

variable {F : LocalFieldPackage.{uF}}
variable (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

private theorem isTopologicalRing :
    letI := T.topology
    IsTopologicalRing F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

/-- The normalized Jacquet module `r_P(ρ)` of an actual p-adic field, using the
full explicit block modulus `T.leviModulus B`. -/
def normalizedJacquet (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    Representation ℂ (B.Levi F.Carrier) (B.JacquetModule ρ) :=
  B.normalizedJacquetOf (T.leviModulus B) ρ

/-- The Levi acts by `δ_P(m)^(-1/2)` times the action of the embedded block
diagonal matrix. -/
theorem normalizedJacquet_mk (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (m : B.Levi F.Carrier) (v : V) :
    T.normalizedJacquet B ρ m (B.jacquetMk ρ v) =
      (((NNReal.sqrt (T.leviModulus B m : ℝ≥0) : ℝ) : ℂ))⁻¹ •
        B.jacquetMk ρ (ρ (B.leviEmbedding F.Carrier m) v) :=
  B.normalizedJacquetOf_mk _ ρ m v

/-- The normalizing scalar is the inverse of the induction half. -/
theorem normalizedJacquet_mk_eq_inv_halfModulus
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (m : B.Levi F.Carrier) (v : V) :
    T.normalizedJacquet B ρ m (B.jacquetMk ρ v) =
      ((T.leviHalfModulus B m)⁻¹ : ℂˣ) •
        B.jacquetMk ρ (ρ (B.leviEmbedding F.Carrier m) v) := by
  rw [normalizedJacquet_mk, Units.smul_def, Units.val_inv_eq_inv_val,
    leviHalfModulus_apply]

/-- The Jacquet map of an actual intertwiner. -/
def normalizedJacquetMap {ρ : Representation ℂ (GeneralLinear n F.Carrier) V}
    {τ : Representation ℂ (GeneralLinear n F.Carrier) W} (f : ρ.IntertwiningMap τ) :
    (T.normalizedJacquet B ρ).IntertwiningMap (T.normalizedJacquet B τ) :=
  B.normalizedJacquetOfMap (T.leviModulus B) f

/-- The normalized Jacquet functor of canonical smooth categories. -/
def normalizedJacquetFunctor :
    letI := T.generalLinearTopology n
    letI := T.leviTopology B
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier) :=
  letI := T.topology
  letI := T.isTopologicalRing
  B.normalizedJacquetFunctorOf (T.leviModulus B) (T.isOpen_ker_leviModulus B)

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
namespace Langlands.AllFieldBZ.LocalFieldPackage
universe uF uV

variable (F : LocalFieldPackage.{uF})
variable {n : ℕ} (B : GeneralLinear.BlockShape n)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

end Langlands.AllFieldBZ.LocalFieldPackage
