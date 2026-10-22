/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Worker 174

The quotient-lift construction is adapted from Mathlib's `Rep.indResHomEquiv`.
-/
import Langlands.Weil.Representation.RestrictionInduction

/-!
# Generator-form Frobenius reciprocity

The quotient lift is written with independent source and target carrier universes.
-/

noncomputable section

namespace Langlands.Weil

open Representation

universe uG uV uU

variable {G : Type uG} [Group G] (H : Subgroup G)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {U : Type uU} [AddCommGroup U] [Module ℂ U]
  (ρ : Representation ℂ H V) (σ : Representation ℂ G U)

/-- Extend a subgroup intertwiner through the actual induction coinvariants. -/
private def inductionExtension (f : ρ.IntertwiningMap (σ.comp H.subtype)) :
    (ρ.ind H.subtype).IntertwiningMap σ :=
  ⟨Coinvariants.lift _
    (TensorProduct.lift <| (Finsupp.lift _ _ _ fun h => σ h⁻¹ ∘ₗ f.toLinearMap) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap)
    (fun g => by
      ext h x
      simp only [LinearMap.coe_comp, Function.comp_apply, MonoidAlgebra.lsingle_apply]
      simp [ofMulAction_single, mul_inv_rev, IntertwiningMap.isIntertwining ρ (σ.comp H.subtype) f g]),
    fun g => by ext; simp⟩

private lemma inductionExtension_mk (f : ρ.IntertwiningMap (σ.comp H.subtype))
    (h : G) (v : V) :
    inductionExtension H ρ σ f (IndV.mk H.subtype ρ h v) = σ h⁻¹ (f v) := by
  simp [inductionExtension]

/-- The exact generator-form reciprocity target, without index or dimension assumptions. -/
theorem representationInductionReciprocity :
    RepresentationInductionReciprocity.{uG, uV, uU} := by
  intro G _ H V _ _ U _ _ ρ σ f
  refine ⟨inductionExtension H ρ σ f, ?_, ?_⟩
  · intro v
    rw [inductionExtension_mk]
    simp
  · intro F hF
    apply IntertwiningMap.ext
    apply IndV.hom_ext
    intro h
    apply LinearMap.ext
    intro v
    change F (IndV.mk H.subtype ρ h v) =
      inductionExtension H ρ σ f (IndV.mk H.subtype ρ h v)
    rw [inductionExtension_mk]
    simpa only [ind_mk, inv_inv, one_mul, hF] using
      IntertwiningMap.isIntertwining (ρ.ind H.subtype) σ F h⁻¹
        (IndV.mk H.subtype ρ 1 v)

-- Check the complete unapplied constant, preserving all three universe parameters.
example : RepresentationInductionReciprocity.{uG, uV, uU} :=
  @representationInductionReciprocity.{uG, uV, uU}

end Langlands.Weil
