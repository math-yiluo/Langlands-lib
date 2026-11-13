import Langlands.Representation.CuspidalSupport.DeterminantUnit
import Langlands.AllField.Group.GL.NormalizedCharacter
/-! The determinant-unit subgroup of a product Levi and smooth restriction. -/

noncomputable section

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding continuous_determinantUnitInclusion determinantUnitInclusion determinantUnitInclusion_apply determinantUnitOpenSubgroup determinantUnitRestriction determinantUnitRestriction_apply determinantUnitSubgroup determinantUnitSubgroup_normal isOpen_determinantUnitSubgroup isSmooth_determinantUnitRestriction leviDeterminantNorm leviDeterminantNorm_apply mem_determinantUnitSubgroup mem_determinantUnitSubgroup_iff_normalizedAbs
open Langlands.AllField.CuspidalSupport

open CategoryTheory
open Langlands.GeneralLinear
open scoped NNReal

universe uF uV uW uX

variable {F : Type uF} [Field F]
  (T : LocalFieldData F) {n : ℕ} (B : BlockShape n)

/-- The tuple of residue-normalized determinant absolute values, one per block. -/
def leviDeterminantNorm : B.Levi F →* (Fin B.length → ℝ≥0ˣ) where
  toFun g i := T.determinantNorm (B.size i) (g i)
  map_one' := by funext i; exact map_one (T.determinantNorm (B.size i))
  map_mul' g h := by funext i; exact map_mul (T.determinantNorm (B.size i)) (g i) (h i)

@[simp] theorem leviDeterminantNorm_apply (g : B.Levi F) (i : Fin B.length) :
    leviDeterminantNorm T B g i = T.determinantNorm (B.size i) (g i) := rfl

/-- BZ76's `G°`: every block determinant has normalized absolute value one. -/
def determinantUnitSubgroup : Subgroup (B.Levi F) :=
  (leviDeterminantNorm T B).ker

@[simp] theorem mem_determinantUnitSubgroup (g : B.Levi F) :
    g ∈ determinantUnitSubgroup T B ↔
      ∀ i, T.determinantNorm (B.size i) (g i) = 1 := by
  change leviDeterminantNorm T B g = 1 ↔ _
  exact funext_iff

theorem mem_determinantUnitSubgroup_iff_normalizedAbs (g : B.Levi F) :
    g ∈ determinantUnitSubgroup T B ↔
      ∀ i, T.normalizedAbs (GeneralLinear.determinant (g i) : F) = 1 := by
  rw [mem_determinantUnitSubgroup]
  apply forall_congr'
  intro i
  rw [← Units.val_inj, ← NNReal.coe_inj]
  rfl

instance determinantUnitSubgroup_normal : (determinantUnitSubgroup T B).Normal :=
  inferInstanceAs (leviDeterminantNorm T B).ker.Normal

/-- The actual inclusion of `G°` in the product Levi. -/
abbrev determinantUnitInclusion : determinantUnitSubgroup T B →* B.Levi F :=
  (determinantUnitSubgroup T B).subtype

@[simp] theorem determinantUnitInclusion_apply (g : determinantUnitSubgroup T B) :
    determinantUnitInclusion T B g = g.val := rfl

section Topology

/-- Openness follows from the finitely many open determinant kernels. -/
theorem isOpen_determinantUnitSubgroup :
    letI := T.topology
    IsOpen (determinantUnitSubgroup T B : Set (B.Levi F)) := by
  let := T.topology
  have he : (determinantUnitSubgroup T B : Set (B.Levi F)) =
      ⋂ i : Fin B.length,
        (fun g : B.Levi F => g i) ⁻¹'
          ((T.determinantNorm (B.size i)).ker : Set (GeneralLinear (B.size i) F)) := by
    ext g
    simpa only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_ker] using
      mem_determinantUnitSubgroup T B g
  rw [he]
  exact isOpen_iInter_of_finite fun i =>
    (T.isOpen_ker_determinantNorm (B.size i)).preimage (continuous_apply i)

/-- The same concrete subgroup packaged as an open subgroup. -/
def determinantUnitOpenSubgroup :
    letI := T.topology
    OpenSubgroup (B.Levi F) := by
  letI := T.topology
  exact { toSubgroup := determinantUnitSubgroup T B
          isOpen' := isOpen_determinantUnitSubgroup T B }

theorem continuous_determinantUnitInclusion :
    letI := T.topology
    Continuous (determinantUnitInclusion T B) := by
  let := T.topology
  exact continuous_subtype_val

end Topology

variable {V : Type uV} {W : Type uW} {X : Type uX}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X]

/-- Restrict the actual action along the subgroup inclusion, retaining its carrier. -/
def determinantUnitRestriction (ρ : Representation ℂ (B.Levi F) V) :
    Representation ℂ (determinantUnitSubgroup T B) V :=
  ρ.comp (determinantUnitInclusion T B)

@[simp] theorem determinantUnitRestriction_apply
    (ρ : Representation ℂ (B.Levi F) V)
    (g : determinantUnitSubgroup T B) (v : V) :
    determinantUnitRestriction T B ρ g v = ρ g.val v := rfl

section Smooth

theorem isSmooth_determinantUnitRestriction
    {ρ : Representation ℂ (B.Levi F) V} :
    letI := T.topology
    IsSmooth ρ → IsSmooth (determinantUnitRestriction T B ρ) := by
  let := T.topology
  exact isSmooth_comp (determinantUnitInclusion T B)
    (continuous_determinantUnitInclusion T B)

end Smooth

end Langlands.AllField.CuspidalSupport
