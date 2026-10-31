import Langlands.Algebra.FilteredRetractionSymmetrization

/-! # Filtered spanning after removing stable Lie directions -/

noncomputable section
universe v w
set_option autoImplicit false

namespace Langlands.Algebra.UniversalEnveloping

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type) (L : Type v) [Field R] [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

/-- Symmetrizations of bounded symmetric tensors after the specified linear removal. -/
def retractedSymmetrizationSpan (f : L →ₗ[R] L) (d : ℕ) : Submodule R U :=
  (symmetricDegreeFiltration R L d).map
    ((symmetricAlgebraSymmetrize R L).comp (symmetricLinearLift R L f).toLinearMap)

theorem retractedSymmetrizationSpan_mono (f : L →ₗ[R] L) :
    Monotone (retractedSymmetrizationSpan R L f) := by
  intro d e h
  exact Submodule.map_mono (symmetricDegreeFiltration_mono R L h)

theorem retractedSymmetrizationSpan_le (f : L →ₗ[R] L) (d : ℕ) :
    retractedSymmetrizationSpan R L f d ≤ degreeFiltration R L d := by
  rintro a ⟨P, hP, rfl⟩
  exact symmetricAlgebraSymmetrize_mem_degreeFiltration R L
    (symmetricLinearLift_mem_symmetricDegreeFiltration R L f hP)

theorem one_mem_retractedSymmetrizationSpan (f : L →ₗ[R] L) (d : ℕ) :
    (1 : U) ∈ retractedSymmetrizationSpan R L f d := by
  refine ⟨1, ?_, ?_⟩
  · exact prod_mem_symmetricDegreeFiltration R L [] (by simp)
  · simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_one,
      symmetricAlgebraSymmetrize_one]

section Module

variable [CharZero R] {V : Type w} [AddCommGroup V] [Module R V]
  [Module (UniversalEnvelopingAlgebra R L) V]
  [IsScalarTower R (UniversalEnvelopingAlgebra R L) V]

/-- A stable subspace has the same filtered orbit span after removing the stable
Lie directions before symmetrization. No injectivity or idempotence is required. -/
theorem retractedSymmetrizationSpan_smul_eq
    (M : Submodule R L) (f : L →ₗ[R] L) (hf : ∀ X, X - f X ∈ M)
    (W : Submodule R V)
    (hW : ∀ X ∈ M, ∀ w ∈ W, UniversalEnvelopingAlgebra.ι R X • w ∈ W)
    (d : ℕ) :
    retractedSymmetrizationSpan R L f d • W = degreeFiltration R L d • W := by
  apply le_antisymm
  · exact Submodule.smul_mono_left (retractedSymmetrizationSpan_le R L f d)
  · induction d with
    | zero =>
      rw [degreeFiltration_zero, Submodule.one_smul]
      intro w hw
      simpa only [one_smul] using Submodule.smul_mem_smul
        (one_mem_retractedSymmetrizationSpan R L f 0) hw
    | succ d ih =>
      apply Submodule.smul_le.mpr
      intro a ha w hw
      obtain ⟨P, hP⟩ := symmetricAlgebraSymmetrizeDegree_surjective R L (d + 1) ⟨a, ha⟩
      have heq : symmetricAlgebraSymmetrize R L P.val = a := congrArg Subtype.val hP
      have herr : (a - symmetricAlgebraSymmetrize R L
          (symmetricLinearLift R L f P.val)) • w ∈ degreeFiltration R L d • W := by
        apply rightGeneratorRemainder_smul_mem R L M W hW ?_ hw
        simpa only [heq, Nat.add_sub_cancel] using
          symmetricAlgebraSymmetrize_sub_retraction_mem R L M f hf P.property
      have hlow : degreeFiltration R L d • W ≤
          retractedSymmetrizationSpan R L f (d + 1) • W := by
        exact ih.trans (Submodule.smul_mono_left
          (retractedSymmetrizationSpan_mono R L f (Nat.le_succ d)))
      have hmain : symmetricAlgebraSymmetrize R L
          (symmetricLinearLift R L f P.val) • w ∈
          retractedSymmetrizationSpan R L f (d + 1) • W :=
        Submodule.smul_mem_smul ⟨P.val, P.property, rfl⟩ hw
      simpa only [sub_smul, sub_add_cancel] using
        (retractedSymmetrizationSpan R L f (d + 1) • W).add_mem (hlow herr) hmain

end Module

end Langlands.Algebra.UniversalEnveloping
