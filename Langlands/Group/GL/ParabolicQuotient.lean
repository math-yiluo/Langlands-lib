import Langlands.Group.GL.OppositeBlocks
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Algebra.Group.Quotient

/-! Concrete quotient and ambient-subgroup bridges for standard GL parabolics. -/

noncomputable section

open scoped Pointwise

namespace Langlands.GeneralLinear.BlockShape

universe uR

variable {n : ℕ} (B : BlockShape n) (R : Type uR) [CommRing R]

/-- The radical in the parabolic and its actual image in GL are isomorphic. -/
def unipotentAmbientEquiv : B.unipotentRadical R ≃* B.unipotentSubgroup R :=
  (B.unipotentRadical R).equivMapOfInjective
    (B.parabolic R).subtype Subtype.val_injective

@[simp] theorem unipotentAmbientEquiv_val (u : B.unipotentRadical R) :
    (B.unipotentAmbientEquiv R u : GeneralLinear n R) = u.val.val := rfl

/-- The embedded Levi lies in the actual upper parabolic. -/
theorem leviSubgroup_le_parabolic : B.leviSubgroup R ≤ B.parabolic R :=
  fun g hg => (B.leviAsParabolic R ⟨g, hg⟩).property

/-- The ambient radical lies in the actual upper parabolic. -/
theorem unipotentSubgroup_le_parabolic : B.unipotentSubgroup R ≤ B.parabolic R := by
  rintro g ⟨u, _, rfl⟩
  exact u.property

/-- The embedded Levi and radical meet only in the identity matrix. -/
theorem leviSubgroup_inf_unipotentSubgroup :
    B.leviSubgroup R ⊓ B.unipotentSubgroup R = ⊥ := by
  apply le_antisymm
  · rintro g ⟨⟨m, rfl⟩, u, hu, heq⟩
    have heqP : u = B.leviInParabolic R m := Subtype.ext heq
    have hm : m = 1 := by
      change B.leviProjection R u = 1 at hu
      simpa only [heqP, leviProjection_section] using hu
    change B.leviEmbedding R m = 1
    rw [hm, map_one]
  · exact bot_le

/-- The actual parabolic is the set product of its ambient radical and Levi. -/
theorem parabolic_eq_unipotent_mul_levi :
    (B.parabolic R : Set (GeneralLinear n R)) =
      (B.unipotentSubgroup R : Set (GeneralLinear n R)) *
        (B.leviSubgroup R : Set (GeneralLinear n R)) := by
  ext g
  constructor
  · intro hg
    let q : B.parabolic R := ⟨g, hg⟩
    refine ⟨B.unipotentAmbientEquiv R (B.unipotentPart R q),
      (B.unipotentAmbientEquiv R (B.unipotentPart R q)).property,
      B.leviEmbedding R (B.leviProjection R q),
      ⟨B.leviProjection R q, rfl⟩, ?_⟩
    exact congrArg Subtype.val ((B.decomposition R).symm_apply_apply q)
  · rintro ⟨u, hu, m, hm, rfl⟩
    exact (B.parabolic R).mul_mem
      (B.unipotentSubgroup_le_parabolic R hu) (B.leviSubgroup_le_parabolic R hm)

/-- The opposite product order required by the general semidirect interface. -/
theorem parabolic_eq_levi_mul_unipotent :
    (B.parabolic R : Set (GeneralLinear n R)) =
      (B.leviSubgroup R : Set (GeneralLinear n R)) *
        (B.unipotentSubgroup R : Set (GeneralLinear n R)) := by
  rw [B.parabolic_eq_unipotent_mul_levi R,
    ← Subgroup.set_mul_normalizer_comm _ _
      (B.leviSubgroup_le_normalizer_unipotentSubgroup R)]

/-- The actual group quotient by the radical is the product Levi. -/
def parabolicQuotientLevi :
    B.parabolic R ⧸ B.unipotentRadical R ≃* B.Levi R :=
  QuotientGroup.quotientKerEquivOfRightInverse (B.leviProjection R)
    (B.leviInParabolic R) (B.leviProjection_section R)

@[simp] theorem parabolicQuotientLevi_mk (g : B.parabolic R) :
    B.parabolicQuotientLevi R (QuotientGroup.mk g) = B.leviProjection R g := rfl

@[simp] theorem parabolicQuotientLevi_symm_apply (m : B.Levi R) :
    (B.parabolicQuotientLevi R).symm m =
      QuotientGroup.mk (B.leviInParabolic R m) := rfl

/-- Conjugation on the radical commutes with its actual ambient inclusion. -/
theorem unipotentAmbientEquiv_leviAction (m : B.Levi R) (u : B.unipotentRadical R) :
    (B.unipotentAmbientEquiv R (B.leviAction R m u) : GeneralLinear n R) =
      B.leviEmbedding R m * (B.unipotentAmbientEquiv R u : GeneralLinear n R) *
        (B.leviEmbedding R m)⁻¹ := rfl

section Topology

variable [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]

/-- The radical equivalence also preserves the actual subgroup topologies. -/
def unipotentAmbientEquivContinuous :
    B.unipotentRadical R ≃ₜ* B.unipotentSubgroup R where
  toMulEquiv := B.unipotentAmbientEquiv R
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    change Continuous (fun u : B.unipotentSubgroup R =>
      (B.unipotentAmbientEquiv R).symm u)
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    have hval (u : B.unipotentSubgroup R) :
        ((B.unipotentAmbientEquiv R).symm u).val.val = u.val :=
      congrArg Subtype.val ((B.unipotentAmbientEquiv R).apply_symm_apply u)
    exact (continuous_subtype_val :
      Continuous (fun u : B.unipotentSubgroup R => u.val)).congr
        (fun u => (hval u).symm)

/-- Closedness of the actual Levi follows from its continuous retraction in P. -/
theorem isClosed_leviSubgroup :
    IsClosed (B.leviSubgroup R : Set (GeneralLinear n R)) := by
  have hclosed : IsClosed (Set.range (B.leviInParabolic R)) := by
    have heq : Set.range (B.leviInParabolic R) =
        {g : B.parabolic R | B.leviInParabolic R (B.leviProjection R g) = g} := by
      ext g
      constructor
      · rintro ⟨m, rfl⟩
        simp
      · intro hg
        exact ⟨B.leviProjection R g, hg⟩
    rw [heq]
    exact isClosed_eq
      ((B.leviInParabolicContinuous R).continuous.comp
        (B.leviProjectionContinuous R).continuous) continuous_id
  change IsClosed (Set.range (B.leviEmbedding R))
  have himage : Subtype.val '' Set.range (B.leviInParabolic R) =
      Set.range (B.leviEmbedding R) := by
    ext g
    constructor
    · rintro ⟨q, ⟨m, rfl⟩, rfl⟩
      exact ⟨m, rfl⟩
    · rintro ⟨m, rfl⟩
      exact ⟨B.leviInParabolic R m, ⟨m, rfl⟩, rfl⟩
  rw [← himage]
  exact (B.isClosed_parabolic R).isClosedMap_subtype_val _ hclosed

end Topology

end Langlands.GeneralLinear.BlockShape
