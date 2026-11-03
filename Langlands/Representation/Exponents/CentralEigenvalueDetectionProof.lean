import Langlands.Representation.Exponents.CentralEigenvalueDetectionStatement
import Langlands.Representation.Exponents.CentralEigencharacterExtensionProof

/-!
# Proof of full-center detection of a central generalized eigenvalue

Intersect a single generalized eigenspace with an admissible fixed space,
and take a common eigenvector of the full center on this finite space.
-/

noncomputable section

namespace Langlands

universe uG uV

/-- A generalized eigenvalue of one central operator is the value of a smooth
full-center exponent. Only the fixed vectors of one open subgroup are made
finite-dimensional. -/
theorem exists_centralExponent_of_generalized_eigenvector
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ)
    (z : Subgroup.center G) (μ : ℂ) (n : ℕ) {v : V}
    (hv : v ≠ 0) (hvμ : ((ρ (z : G) - μ • 1) ^ n) v = 0) :
    ∃ χ : Subgroup.center G →* ℂˣ, IsCentralExponent ρ χ ∧ (χ z : ℂ) = μ := by
  obtain ⟨K, hK⟩ := hρ.1 v
  let W : Submodule ℂ V :=
    Module.End.genEigenspace (ρ (z : G)) μ n ⊓ fixedVectors ρ K.toSubgroup
  have : Module.Finite ℂ (fixedVectors ρ K.toSubgroup) := hρ.2 K
  have : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le inf_le_right
  have hvW : v ∈ W := by
    refine ⟨?_, hK⟩
    change v ∈ Module.End.genEigenspace (ρ (z : G)) μ (n : ℕ∞)
    exact Module.End.mem_genEigenspace_nat.mpr hvμ
  have : Nontrivial W := ⟨⟨⟨v, hvW⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩
  have hcomm : ∀ a : Subgroup.center G, ∀ g : G, ρ (a : G) * ρ g = ρ g * ρ (a : G) := by
    intro a g
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp a.property g)]
  have hmaps : ∀ a : Subgroup.center G, ∀ w ∈ W, ρ (a : G) w ∈ W := by
    intro a w hw
    refine ⟨?_, ?_⟩
    · exact Module.End.mapsTo_genEigenspace_of_comp (ρ (a : G))
        (hcomm a (z : G)).symm μ n hw.1
    · intro g
      change ρ (g : G) (ρ (a : G) w) = ρ (a : G) w
      rw [← Module.End.mul_apply, ← hcomm a (g : G), Module.End.mul_apply]
      exact congrArg (ρ (a : G)) (hw.2 g)
  let f : Subgroup.center G → Module.End ℂ W :=
    fun a => (ρ (a : G)).restrict (hmaps a)
  have hfc : ∀ a b, Commute (f a) (f b) := by
    intro a b
    refine LinearMap.ext fun w => Subtype.ext ?_
    change ρ (a : G) (ρ (b : G) w) = ρ (b : G) (ρ (a : G) w)
    exact congrArg (fun T : Module.End ℂ V => T (w : V)) (hcomm a (b : G))
  obtain ⟨w, hw, hweigen⟩ := EndomorphismBound.exists_common_eigenvector f hfc
  have hwV : (w : V) ≠ 0 := fun h => hw (Subtype.ext h)
  have heigen : ∀ a, ∃ c : ℂ, (ρ.comp (Subgroup.center G).subtype) a (w : V) =
      c • (w : V) := by
    intro a
    obtain ⟨c, hc⟩ := hweigen a
    exact ⟨c, congrArg Subtype.val hc⟩
  obtain ⟨χ, hχ⟩ := EndomorphismBound.exists_character_of_forall_eigen
    (ρ.comp (Subgroup.center G).subtype) hwV heigen
  refine ⟨χ, ⟨?_, ?_⟩, ?_⟩
  · let KZ := OpenSubgroup.comap (Subgroup.center G).subtype continuous_subtype_val K
    refine Subgroup.isOpen_mono (H₁ := KZ.toSubgroup) ?_ KZ.isOpen
    intro a ha
    rw [MonoidHom.mem_ker]
    have hfix : ρ (a : G) (w : V) = (w : V) := w.2.2 ⟨(a : G), ha⟩
    have hscalar : ((χ a : ℂ) - 1) • (w : V) = 0 := by
      rw [sub_smul, one_smul, ← hχ a]
      exact sub_eq_zero.mpr hfix
    exact Units.ext (sub_eq_zero.mp ((smul_eq_zero.mp hscalar).resolve_right hwV))
  · have hmem : (w : V) ∈ generalizedCentralCharacterSpace ρ χ :=
      (mem_generalizedCentralCharacterSpace ρ χ (w : V)).mpr
      ⟨1, fun a => by simpa using sub_eq_zero.mpr (hχ a)⟩
    intro hbot
    rw [hbot] at hmem
    change (w : V) ∈ (⊥ : Submodule ℂ V) at hmem
    exact hwV ((Submodule.mem_bot ℂ).mp hmem)
  · apply eq_of_eigen_of_mem_genEigenspace (ρ (z : G)) hwV (hχ z) (k := n)
    exact Module.End.mem_genEigenspace_nat.mp w.2.1

/-- Full-center detection of central generalized eigenvalues on admissible
complex representations, with independent group and carrier universes. -/
theorem centralEigenvalueDetection : CentralEigenvalueDetectionStatement.{uG, uV} := by
  intro G _ _ _ V _ _ ρ hρ z μ n v hv hvμ
  exact exists_centralExponent_of_generalized_eigenvector ρ hρ z μ n hv hvμ

end Langlands
