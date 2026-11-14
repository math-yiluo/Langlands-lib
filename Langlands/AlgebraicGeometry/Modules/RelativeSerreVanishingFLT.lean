import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule
import Langlands.AnthropicFLT.Theorems.Thm_ProjSpaceCech_GradedModule_exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule

/-! # Relative Serre vanishing for coherent presheaves on closed subschemes of projective space -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase
  AlgebraicGeometry.OModulePresheaf.FamilyFrames.module
  AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup
attribute [local instance] MvPolynomial.gradedAlgebra

namespace Langlands.AlgebraicGeometry.Modules.CechBridge

/-- **Relative Serre vanishing** (FLT Čech form). Let `A` be noetherian and `P ⟶ ℙʳ_A` a closed
immersion over `Spec A`. For every coherent quasi-coherent presheaf `G` on `P`, the higher Čech
cohomology of `G ⊗ O(d)` on the pulled-back standard cover vanishes for all large `d`. This is the
constant-family case (one frame, the identity) of the FLT port's family theorem. -/
theorem exists_forall_subsingleton_HSucc_tensor_twist {A : Type u} [CommRing A]
    [IsNoetherianRing A] {r : ℕ} {P : Scheme.{u}}
    (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)) [IsClosedImmersion ι]
    {q : P ⟶ Spec (CommRingCat.of A)} (hιq : ι ≫ ProjSpace.π A r = q) (G : OModulePresheaf q)
    (hc : G.IsCoherent) (hq : G.IsQuasicoherent) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ i : ℕ,
      Subsingleton ((G.tensor (ProjSpace.twist q ι d)).HSucc (ProjSpace.stdCoverPullback ι) i) := by
  let G' : ℕ → OModulePresheaf q := fun _ => G
  let θ : Fin 1 → ∀ k : ℕ, OModulePresheaf.AffHom (G' k) (G' (k + 1)) :=
    fun _ _ => OModulePresheaf.AffHom.id G
  have hθ : OModulePresheaf.YComm G' θ := by
    intro m m' k U x
    rw [Subsingleton.elim m m']
  have hgen : ∀ (k : ℕ) (U : P.affineOpens),
      (⨆ m : Fin 1, LinearMap.range ((θ m k).app U)) = ⊤ := by
    intro k U
    rw [eq_top_iff]
    intro x _
    refine Submodule.mem_iSup_of_mem 0 ⟨x, ?_⟩
    rfl
  obtain ⟨D, hD, h, hinj, hsat⟩ :=
    OModulePresheaf.exists_isFG_hom_injective_saturated_familyFramesGradedModule ι hιq G'
      (fun _ => hc) (fun _ => hq) θ hθ hgen
  obtain ⟨d₀, hd₀⟩ :=
    ProjSpaceCech.GradedModule.exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated
      (OModulePresheaf.familyFramesGradedModule ι G' θ hθ) D hD h hinj hsat
  refine ⟨d₀.toNat, fun d hd i => ?_⟩
  have hv := hd₀ (d : ℤ) (by omega) (i + 1) (Nat.succ_le_succ (Nat.zero_le i))
  exact OModulePresheaf.subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule
    ι G' (fun _ => hq) θ hθ d 0 i hv

end Langlands.AlgebraicGeometry.Modules.CechBridge
