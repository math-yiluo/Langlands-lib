import Langlands.Weil.Representation.Operations
import Langlands.Weil.Representation.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.GroupWithZero

/-! # Determinant and rank-one character normalization -/

noncomputable section

namespace Langlands.Weil

universe uG uV

private theorem continuous_det_moduleTopology
    (V : Type uV) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] :
    let : TopologicalSpace (Module.End ℂ V) := moduleTopology ℂ (Module.End ℂ V)
    Continuous (LinearMap.det : Module.End ℂ V → ℂ) := by
  classical
  let : TopologicalSpace (Module.End ℂ V) := moduleTopology ℂ (Module.End ℂ V)
  let b := Module.finBasis ℂ V
  have hc := IsModuleTopology.continuous_of_linearMap
    (LinearMap.toMatrix b b).toLinearMap
  change Continuous (fun f => LinearMap.toMatrix b b f) at hc
  simpa only [LinearMap.det_toMatrix] using hc.matrix_det

private theorem eq_det_smul_one_of_finrank_one
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (h : Module.finrank ℂ V = 1) (f : Module.End ℂ V) :
    f = LinearMap.det f • (1 : Module.End ℂ V) := by
  obtain ⟨c, hc, _⟩ := f.existsUnique_eq_smul_id_of_finrank_eq_one h
  rw [hc]
  simp only [LinearMap.det_smul, h, pow_one, LinearMap.det_id, mul_one]
  rfl

/-- Every continuous finite-dimensional complex representation has a unique
continuous determinant character, and rank-one representations are equivalent
to exactly one continuous scalar-character representation. -/
theorem representationCharacterNormalization :
    RepresentationCharacterNormalization.{uG, uV} := by
  intro G _ _ V _ _ _ ρ
  let : TopologicalSpace (Module.End ℂ V) := moduleTopology ℂ (Module.End ℂ V)
  intro hρ
  let δ := FiniteRepresentation.determinantCharacter (FiniteRepresentation.of ρ)
  have hδ : Continuous δ := by
    apply Units.isEmbedding_val₀.continuous_iff.mpr
    exact (continuous_det_moduleTopology V).comp hρ
  have hδval (g : G) : (δ g : ℂ) = LinearMap.det (ρ g) := rfl
  constructor
  · refine ⟨δ, ⟨hδ, hδval⟩, ?_⟩
    intro η hη
    ext g
    exact (hη.2 g).trans (hδval g).symm
  · intro hdim
    obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one hdim
    have he : Nonempty (ρ.Equiv (Langlands.characterRepresentation δ)) := by
      refine ⟨{ toLinearEquiv := e.symm, isIntertwining' := ?_ }⟩
      intro g
      ext v
      change e.symm (ρ g v) = (δ g : ℂ) • e.symm v
      rw [eq_det_smul_one_of_finrank_one hdim (ρ g)]
      simp only [LinearMap.smul_apply, Module.End.one_apply, map_smul, hδval]
    refine ⟨δ, ⟨hδ, he⟩, ?_⟩
    rintro η ⟨_, ⟨f⟩⟩
    have hf := FiniteRepresentation.determinantCharacter_eq
      (A := FiniteRepresentation.of ρ)
      (B := FiniteRepresentation.of (Langlands.characterRepresentation η)) f
    ext g
    have hfg := congrArg (fun χ : G →* ℂˣ => (χ g : ℂ)) hf
    change (η g : ℂ) = LinearMap.det (ρ g)
    change LinearMap.det (ρ g) =
      LinearMap.det (Langlands.characterRepresentation η g) at hfg
    rw [LinearMap.det_ring] at hfg
    change LinearMap.det (ρ g) = (η g : ℂ) * 1 at hfg
    simpa only [mul_one] using hfg.symm

end Langlands.Weil
