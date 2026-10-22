import Langlands.Group.GL.Basic
import Langlands.Group.GL.Padic
import Mathlib.Data.Matrix.Block
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Standard block sum maps between actual general linear groups
-/

namespace Langlands.GeneralLinear

universe u

variable {R : Type u} [CommRing R] {n m : ℕ}

private def blockSumCoordinates :
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

/-- Put two invertible matrices in successive diagonal blocks. -/
def blockSum : Langlands.GeneralLinear n R × Langlands.GeneralLinear m R →*
    Langlands.GeneralLinear (n + m) R :=
  (reindex (R := R) finSumFinEquiv).toMonoidHom.comp blockSumCoordinates

/-- The first diagonal block has the original entries. -/
@[simp] theorem blockSum_apply_left (g : Langlands.GeneralLinear n R)
    (h : Langlands.GeneralLinear m R) (i j : Fin n) :
    blockSum (g, h) (i.castAdd m) (j.castAdd m) = g i j := by
  change Matrix.fromBlocks g.val 0 0 h.val
    (finSumFinEquiv.symm (i.castAdd m)) (finSumFinEquiv.symm (j.castAdd m)) = _
  simp

/-- The second diagonal block has the original entries. -/
@[simp] theorem blockSum_apply_right (g : Langlands.GeneralLinear n R)
    (h : Langlands.GeneralLinear m R) (i j : Fin m) :
    blockSum (g, h) (i.natAdd n) (j.natAdd n) = h i j := by
  change Matrix.fromBlocks g.val 0 0 h.val
    (finSumFinEquiv.symm (i.natAdd n)) (finSumFinEquiv.symm (j.natAdd n)) = _
  simp

/-- The upper off-diagonal block is zero. -/
@[simp] theorem blockSum_apply_left_right (g : Langlands.GeneralLinear n R)
    (h : Langlands.GeneralLinear m R) (i : Fin n) (j : Fin m) :
    blockSum (g, h) (i.castAdd m) (j.natAdd n) = 0 := by
  change Matrix.fromBlocks g.val 0 0 h.val
    (finSumFinEquiv.symm (i.castAdd m)) (finSumFinEquiv.symm (j.natAdd n)) = 0
  simp

/-- The lower off-diagonal block is zero. -/
@[simp] theorem blockSum_apply_right_left (g : Langlands.GeneralLinear n R)
    (h : Langlands.GeneralLinear m R) (i : Fin m) (j : Fin n) :
    blockSum (g, h) (i.natAdd n) (j.castAdd m) = 0 := by
  change Matrix.fromBlocks g.val 0 0 h.val
    (finSumFinEquiv.symm (i.natAdd n)) (finSumFinEquiv.symm (j.castAdd m)) = 0
  simp

/-- The standard rank inclusion `g ↦ diag(g, I_m)`. -/
def rankInclusion (m : ℕ) : Langlands.GeneralLinear n R →*
    Langlands.GeneralLinear (n + m) R :=
  blockSum.comp
    { toFun g := (g, 1)
      map_one' := rfl
      map_mul' _ _ := by simp }

/-- Standard rank inclusion is injective, including in zero rank. -/
theorem rankInclusion_injective (m : ℕ) :
    Function.Injective (rankInclusion (R := R) (n := n) m) := by
  intro g h he
  apply Units.ext
  ext i j
  have hc := congrArg (fun k : Langlands.GeneralLinear (n + m) R =>
    k (i.castAdd m) (j.castAdd m)) he
  simpa only [rankInclusion, MonoidHom.coe_comp, Function.comp_apply,
    MonoidHom.coe_mk, OneHom.coe_mk, blockSum_apply_left] using hc

section Topology

variable [TopologicalSpace R]

private theorem continuous_blockSumCoordinates :
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

/-- Block sum is a continuous homomorphism for any coefficient topology. -/
def blockSumContinuous :
    ContinuousMonoidHom (Langlands.GeneralLinear n R × Langlands.GeneralLinear m R)
      (Langlands.GeneralLinear (n + m) R) where
  toMonoidHom := blockSum
  continuous_toFun :=
    (reindexContinuous (R := R) finSumFinEquiv).continuous.comp
      continuous_blockSumCoordinates

/-- Standard rank inclusion is continuous for the actual matrix-unit topologies. -/
def rankInclusionContinuous (m : ℕ) :
    ContinuousMonoidHom (Langlands.GeneralLinear n R)
      (Langlands.GeneralLinear (n + m) R) where
  toMonoidHom := rankInclusion m
  continuous_toFun := blockSumContinuous.continuous.comp
    (continuous_id.prodMk continuous_const)

end Topology
end Langlands.GeneralLinear

namespace Langlands.PadicField

universe u

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p}

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

/-- Continuous block sum for the canonical topology of every algebraic p-adic field. -/
noncomputable abbrev canonicalBlockSum (F : PadicField.{u} p) (n m : ℕ) :
    letI := F.canonicalTopologicalData.topology
    ContinuousMonoidHom (GeneralLinear n F.Carrier × GeneralLinear m F.Carrier)
      (GeneralLinear (n + m) F.Carrier) :=
  F.canonicalTopologicalData.blockSum n m

/-- Continuous standard rank inclusion for the canonical p-adic topology. -/
noncomputable abbrev canonicalRankInclusion (F : PadicField.{u} p) (n m : ℕ) :
    letI := F.canonicalTopologicalData.topology
    ContinuousMonoidHom (GeneralLinear n F.Carrier) (GeneralLinear (n + m) F.Carrier) :=
  F.canonicalTopologicalData.rankInclusion n m

end Langlands.PadicField
