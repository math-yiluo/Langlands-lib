import Langlands.Representation.Intertwining.PQRegularity
import Langlands.Representation.Exponents.Jacquet

/-! # Action kernels and generalized characters -/

noncomputable section

namespace Langlands.PQKernelCharacters

variable {B : Type*} [CommGroup B]
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Extend a complex group character to its scalar group-algebra homomorphism. -/
def characterAlgebraHom (χ : B →* ℂˣ) : MonoidAlgebra ℂ B →ₐ[ℂ] ℂ :=
  MonoidAlgebra.lift ℂ ℂ B ((Units.coeHom ℂ).comp χ)

/-- Every vector with generalized character χ is a generalized eigenvector
for every group-algebra element, with eigenvalue given by the extended χ. -/
theorem mem_maxGenEigenspace_action (ρ : Representation ℂ B V) (χ : B →* ℂˣ)
    (d : ℕ) {v : V} (hv : v ∈ characterSpace ρ χ d) (c : MonoidAlgebra ℂ B) :
    v ∈ (Representation.asAlgebraHom ρ c).maxGenEigenspace (characterAlgebraHom χ c) := by
  induction c using MonoidAlgebra.induction_linear with
  | zero =>
    apply (Module.End.mem_maxGenEigenspace _ _ _).mpr
    exact ⟨1, by simp⟩
  | add a b ha hb =>
    simpa only [map_add, Module.End.maxGenEigenspace, top_add] using
      Module.End.genEigenspace_inf_le_add
        (Representation.asAlgebraHom ρ a) (Representation.asAlgebraHom ρ b)
        (characterAlgebraHom χ a) (characterAlgebraHom χ b) ⊤ ⊤
        ((Commute.all a b).map (Representation.asAlgebraHom ρ)) ⟨ha, hb⟩
  | single b z =>
    have hvb : v ∈ Module.End.maxGenEigenspace (ρ b) (χ b : ℂ) :=
      (Module.End.mem_maxGenEigenspace _ _ _).mpr ⟨d, (mem_characterSpace ρ χ d v).mp hv b⟩
    simpa only [Representation.asAlgebraHom_single, characterAlgebraHom,
      MonoidAlgebra.lift_single, MonoidHom.coe_comp, Function.comp_apply,
      Units.coeHom_apply, smul_eq_mul] using
      Module.End.genEigenspace_le_smul (ρ b) (χ b : ℂ) z ⊤ hvb

/-- Occurrence of a generalized character puts the entire action kernel in
the kernel of that scalar character. -/
theorem kernel_le_characterKernel (ρ : Representation ℂ B V) (χ : B →* ℂˣ)
    (hχ : IsGeneralizedEigencharacter ρ χ) :
    groupAlgebraKernel ρ (MonoidHom.id B) ≤ RingHom.ker (characterAlgebraHom χ) := by
  obtain ⟨d, v, hv0, hv⟩ := (isGeneralizedEigencharacter_iff ρ χ).mp hχ
  intro c hc
  apply RingHom.mem_ker.mpr
  by_contra hne
  have hvc := mem_maxGenEigenspace_action ρ χ d
    ((mem_characterSpace ρ χ d v).mpr hv) c
  have hc0 : Representation.asAlgebraHom ρ c = 0 :=
    (mem_groupAlgebraKernel_iff ρ (MonoidHom.id B) c).mp hc
  rw [hc0] at hvc
  obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hvc
  have hm' : (-(characterAlgebraHom χ c)) ^ m • v = 0 := by
    simpa only [zero_sub, ← neg_smul, smul_pow, one_pow,
      LinearMap.smul_apply, Module.End.one_apply] using hm
  exact hv0 ((smul_eq_zero.mp hm').resolve_left (pow_ne_zero _ (neg_ne_zero.mpr hne)))

/-- Representations with comaximal action kernels have disjoint generalized
character sets, without any finiteness hypothesis. -/
theorem disjoint_generalizedCharacters (ρ : Representation ℂ B V) (σ : Representation ℂ B W)
    (h : groupAlgebraKernel ρ (MonoidHom.id B) ⊔
      groupAlgebraKernel σ (MonoidHom.id B) = ⊤) :
    Disjoint {χ | IsGeneralizedEigencharacter ρ χ}
      {χ | IsGeneralizedEigencharacter σ χ} := by
  rw [Set.disjoint_left]
  intro χ hρ hσ
  have hle := sup_le (kernel_le_characterKernel ρ χ hρ) (kernel_le_characterKernel σ χ hσ)
  rw [h] at hle
  have h1 : (1 : MonoidAlgebra ℂ B) ∈ RingHom.ker (characterAlgebraHom χ) :=
    hle (Submodule.mem_top)
  have h10 := RingHom.mem_ker.mp h1
  rw [map_one] at h10
  exact one_ne_zero h10

end Langlands.PQKernelCharacters
