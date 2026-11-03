import Langlands.Representation.Exponents.Central
import Langlands.Representation.Exponents.CentralEigencharacterExtensionProof

/-! # Central exponents under embeddings into a scalar central action -/

noncomputable section

namespace Langlands

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

/-- An injective intertwiner preserves every actual full-center exponent,
including its open-kernel condition. -/
theorem isCentralExponent_of_injective
    (f : ρ.IntertwiningMap σ) (hf : Function.Injective f)
    (χ : Subgroup.center G →* ℂˣ) (hχ : IsCentralExponent ρ χ) :
    IsCentralExponent σ χ := by
  refine ⟨hχ.1, ?_⟩
  intro hzero
  apply hχ.2
  apply le_antisymm _ bot_le
  intro v hv
  have hm := map_mem_generalizedCentralCharacterSpace f χ hv
  rw [hzero] at hm
  change f v = 0 at hm
  change v = 0
  apply hf
  simpa using hm

/-- An actual equivalence preserves the entire full-center exponent predicate. -/
theorem isCentralExponent_equiv_iff (e : ρ.Equiv σ)
    (χ : Subgroup.center G →* ℂˣ) :
    IsCentralExponent ρ χ ↔ IsCentralExponent σ χ :=
  ⟨isCentralExponent_of_injective e.toIntertwiningMap e.injective χ,
    isCentralExponent_of_injective e.symm.toIntertwiningMap e.symm.injective χ⟩

/-- Every exponent of a representation embedded into a scalar central action
is the scalar character. No admissibility or finite-length premise is used. -/
theorem centralExponent_eq_of_scalar_injective
    (f : ρ.IntertwiningMap σ) (hf : Function.Injective f)
    (χ₀ : Subgroup.center G →* ℂˣ)
    (hscalar : ∀ (z : Subgroup.center G) (w : W),
      σ (z : G) w = (χ₀ z : ℂ) • w)
    (χ : Subgroup.center G →* ℂˣ) (hχ : IsCentralExponent ρ χ) :
    χ = χ₀ := by
  have hne : (generalizedCentralCharacterSpace ρ χ).toSubmodule ≠ ⊥ := by
    intro hzero
    exact hχ.2 (Subrepresentation.toSubmodule_injective hzero)
  obtain ⟨v, hv, hvzero⟩ := (Submodule.ne_bot_iff _).mp hne
  have hfv : f v ≠ 0 := fun hz => hvzero (hf (by simpa using hz))
  have hm := map_mem_generalizedCentralCharacterSpace f χ hv
  obtain ⟨n, hn⟩ := (mem_generalizedCentralCharacterSpace σ χ (f v)).mp hm
  ext z
  exact (eq_of_eigen_of_mem_genEigenspace (σ (z : G)) hfv
    (hscalar z (f v)) (hn z)).symm

end Langlands
