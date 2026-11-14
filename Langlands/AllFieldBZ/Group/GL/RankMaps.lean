import Langlands.AllFieldBZ.Group.GL.Padic
import Langlands.Group.GL.RankMaps

/-!
# All-field port of `Langlands.Group.GL.RankMaps`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.RankMaps` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.GeneralLinear
open Langlands.GeneralLinear
universe u

variable {R : Type u} [CommRing R] {n m : ℕ}

private def _root_.Langlands.GeneralLinear.blockSumCoordinates :
    Langlands.GeneralLinear n R × Langlands.GeneralLinear m R →*
      Matrix.GeneralLinearGroup (Fin n ⊕ Fin m) R where
  toFun gh :=
    { val := Matrix.fromBlocks gh.1.val 0 0 gh.2.val
      inv := Matrix.fromBlocks (gh.1⁻¹).val 0 0 (gh.2⁻¹).val
      val_inv := by simp [Matrix.fromBlocks_multiply]
      inv_val := by simp [Matrix.fromBlocks_multiply] }
  map_one' := by
    apply Units.ext
    exact Matrix.fromBlocks_one
  map_mul' g h := by
    apply Units.ext
    simp [Matrix.fromBlocks_multiply]

section Topology
variable [TopologicalSpace R]

private theorem _root_.Langlands.GeneralLinear.continuous_blockSumCoordinates :
    Continuous (blockSumCoordinates (R := R) (n := n) (m := m)) := by
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_matrix
    rintro (i | i) (j | j)
    · exact (entry i j).continuous.comp continuous_fst
    · exact continuous_const
    · exact continuous_const
    · exact (entry i j).continuous.comp continuous_snd
  · apply continuous_matrix
    rintro (i | i) (j | j)
    · exact ((continuous_apply j).comp
        ((continuous_apply i).comp
          (show Continuous (fun g : Langlands.GeneralLinear n R => (g⁻¹).val) from
            Units.continuous_coe_inv))).comp continuous_fst
    · exact continuous_const
    · exact continuous_const
    · exact ((continuous_apply j).comp
        ((continuous_apply i).comp
          (show Continuous (fun g : Langlands.GeneralLinear m R => (g⁻¹).val) from
            Units.continuous_coe_inv))).comp continuous_snd

end Topology
end Langlands.AllFieldBZ.GeneralLinear
namespace Langlands.AllFieldBZ.LocalFieldPackage
universe u

variable {F : LocalFieldPackage.{u}}

/-- Continuous block sum for every supplied p-adic topology. -/
def TopologicalData.blockSum (T : F.TopologicalData) (n m : ℕ) :
    letI := T.topology
    ContinuousMonoidHom (GeneralLinear n F.Carrier × GeneralLinear m F.Carrier)
      (GeneralLinear (n + m) F.Carrier) := by
  letI := T.topology
  exact GeneralLinear.blockSumContinuous

/-- Continuous standard rank inclusion for every supplied p-adic topology. -/
def TopologicalData.rankInclusion (T : F.TopologicalData) (n m : ℕ) :
    letI := T.topology
    ContinuousMonoidHom (GeneralLinear n F.Carrier) (GeneralLinear (n + m) F.Carrier) := by
  letI := T.topology
  exact GeneralLinear.rankInclusionContinuous m

end Langlands.AllFieldBZ.LocalFieldPackage
