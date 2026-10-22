import Langlands.Group.GL.Blocks
import Langlands.Group.GL.NormalizedCharacter
import Langlands.Representation.Category.Basic
import Langlands.Representation.Smooth.Transfer.PullbackProof

/-! The determinant-unit subgroup of a product Levi and smooth restriction. -/

noncomputable section

namespace Langlands.CuspidalSupport

open GeneralLinear CategoryTheory
open scoped NNReal

universe uF uV uW uX

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)

/-- The tuple of residue-normalized determinant absolute values, one per block. -/
def leviDeterminantNorm : B.Levi F.Carrier →* (Fin B.length → ℝ≥0ˣ) where
  toFun g i := T.determinantNorm (B.size i) (g i)
  map_one' := by funext i; exact map_one (T.determinantNorm (B.size i))
  map_mul' g h := by funext i; exact map_mul (T.determinantNorm (B.size i)) (g i) (h i)

@[simp] theorem leviDeterminantNorm_apply (g : B.Levi F.Carrier) (i : Fin B.length) :
    leviDeterminantNorm T B g i = T.determinantNorm (B.size i) (g i) := rfl

/-- BZ76's `G°`: every block determinant has normalized absolute value one. -/
def determinantUnitSubgroup : Subgroup (B.Levi F.Carrier) :=
  (leviDeterminantNorm T B).ker

@[simp] theorem mem_determinantUnitSubgroup (g : B.Levi F.Carrier) :
    g ∈ determinantUnitSubgroup T B ↔
      ∀ i, T.determinantNorm (B.size i) (g i) = 1 := by
  change leviDeterminantNorm T B g = 1 ↔ _
  exact funext_iff

theorem mem_determinantUnitSubgroup_iff_normalizedAbs (g : B.Levi F.Carrier) :
    g ∈ determinantUnitSubgroup T B ↔
      ∀ i, T.normalizedAbs (GeneralLinear.determinant (g i) : F.Carrier) = 1 := by
  rw [mem_determinantUnitSubgroup]
  apply forall_congr'
  intro i
  rw [← Units.val_inj, ← NNReal.coe_inj]
  rfl

instance determinantUnitSubgroup_normal : (determinantUnitSubgroup T B).Normal :=
  inferInstanceAs (leviDeterminantNorm T B).ker.Normal

/-- Changing the compatible realization does not change the subgroup. -/
theorem determinantUnitSubgroup_eq (U : F.TopologicalData) :
    determinantUnitSubgroup T B = determinantUnitSubgroup U B := by
  ext g
  simp only [mem_determinantUnitSubgroup, T.determinantNorm_eq U]

/-- The actual inclusion of `G°` in the product Levi. -/
abbrev determinantUnitInclusion : determinantUnitSubgroup T B →* B.Levi F.Carrier :=
  (determinantUnitSubgroup T B).subtype

@[simp] theorem determinantUnitInclusion_apply (g : determinantUnitSubgroup T B) :
    determinantUnitInclusion T B g = g.val := rfl

theorem determinantUnitInclusion_injective :
    Function.Injective (determinantUnitInclusion T B) := Subtype.val_injective

section Topology

/-- Openness follows from the finitely many open determinant kernels. -/
theorem isOpen_determinantUnitSubgroup :
    letI := T.topology
    IsOpen (determinantUnitSubgroup T B : Set (B.Levi F.Carrier)) := by
  let := T.topology
  have he : (determinantUnitSubgroup T B : Set (B.Levi F.Carrier)) =
      ⋂ i : Fin B.length,
        (fun g : B.Levi F.Carrier => g i) ⁻¹'
          ((T.determinantNorm (B.size i)).ker : Set (GeneralLinear (B.size i) F.Carrier)) := by
    ext g
    simpa only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_ker] using
      mem_determinantUnitSubgroup T B g
  rw [he]
  exact isOpen_iInter_of_finite fun i =>
    (T.isOpen_ker_determinantNorm (B.size i)).preimage (continuous_apply i)

/-- The same concrete subgroup packaged as an open subgroup. -/
def determinantUnitOpenSubgroup :
    letI := T.topology
    OpenSubgroup (B.Levi F.Carrier) := by
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
def determinantUnitRestriction (ρ : Representation ℂ (B.Levi F.Carrier) V) :
    Representation ℂ (determinantUnitSubgroup T B) V :=
  ρ.comp (determinantUnitInclusion T B)

@[simp] theorem determinantUnitRestriction_apply
    (ρ : Representation ℂ (B.Levi F.Carrier) V)
    (g : determinantUnitSubgroup T B) (v : V) :
    determinantUnitRestriction T B ρ g v = ρ g.val v := rfl

/-- Restriction keeps the actual equivariant linear map. -/
def determinantUnitRestrictionMap
    {ρ : Representation ℂ (B.Levi F.Carrier) V}
    {σ : Representation ℂ (B.Levi F.Carrier) W} (f : ρ.IntertwiningMap σ) :
    (determinantUnitRestriction T B ρ).IntertwiningMap
      (determinantUnitRestriction T B σ) where
  toLinearMap := f.toLinearMap
  isIntertwining' g := f.isIntertwining' g.val

@[simp] theorem determinantUnitRestrictionMap_apply
    {ρ : Representation ℂ (B.Levi F.Carrier) V}
    {σ : Representation ℂ (B.Levi F.Carrier) W}
    (f : ρ.IntertwiningMap σ) (v : V) :
    determinantUnitRestrictionMap T B f v = f v := rfl

@[simp] theorem determinantUnitRestrictionMap_id
    (ρ : Representation ℂ (B.Levi F.Carrier) V) :
    determinantUnitRestrictionMap T B (Representation.IntertwiningMap.id ρ) =
      Representation.IntertwiningMap.id (determinantUnitRestriction T B ρ) := rfl

@[simp] theorem determinantUnitRestrictionMap_comp
    {ρ : Representation ℂ (B.Levi F.Carrier) V}
    {σ : Representation ℂ (B.Levi F.Carrier) W}
    {τ : Representation ℂ (B.Levi F.Carrier) X}
    (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ) :
    determinantUnitRestrictionMap T B (g.comp f) =
      (determinantUnitRestrictionMap T B g).comp
        (determinantUnitRestrictionMap T B f) := rfl

section Smooth

theorem isSmooth_determinantUnitRestriction
    {ρ : Representation ℂ (B.Levi F.Carrier) V} :
    letI := T.topology
    IsSmooth ρ → IsSmooth (determinantUnitRestriction T B ρ) := by
  let := T.topology
  exact isSmooth_comp (determinantUnitInclusion T B)
    (continuous_determinantUnitInclusion T B)

/-- The actual smooth restriction functor, with identity and composition proved. -/
def determinantUnitRestrictionFunctor :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (determinantUnitSubgroup T B) := by
  letI := T.topology
  exact
    { obj := fun A => SmoothRep.of (determinantUnitRestriction T B A.representation)
        (isSmooth_determinantUnitRestriction T B A.isSmooth)
      map := fun f => SmoothRep.ofHom (determinantUnitRestrictionMap T B (SmoothRep.hom f))
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }

end Smooth

end Langlands.CuspidalSupport
