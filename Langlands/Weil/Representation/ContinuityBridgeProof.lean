import Langlands.Weil.Representation.ContinuityBridgeStatement

/-!
# Compatibility of the bundled and unbundled continuity presentations

Finite-dimensional complex topology uniqueness identifies the canonical module
and operator topologies. The resulting adapters compare the two five-clause
families without proving either family itself.
-/

noncomputable section

universe uG uV

namespace Langlands.Weil

theorem carrier_topology_eq_moduleTopology (V : Type uV)
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℂ V] [T2Space V] :
    (inferInstance : TopologicalSpace V) = moduleTopology ℂ V := by
  let := isModuleTopologyOfFiniteDimensional (𝕜 := ℂ) (E := V)
  exact eq_moduleTopology ℂ V

theorem compatible_carrier_topologies_eq (V : Type uV)
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (τ₁ τ₂ : TopologicalSpace V)
    (h₁ : letI := τ₁; IsTopologicalAddGroup V ∧ ContinuousSMul ℂ V ∧ T2Space V)
    (h₂ : letI := τ₂; IsTopologicalAddGroup V ∧ ContinuousSMul ℂ V ∧ T2Space V) :
    τ₁ = τ₂ := by
  have canonical (τ : TopologicalSpace V)
      (h : letI := τ; IsTopologicalAddGroup V ∧ ContinuousSMul ℂ V ∧ T2Space V) :
      τ = moduleTopology ℂ V := by
    let := τ
    let := h.1
    let := h.2.1
    let := h.2.2
    exact carrier_topology_eq_moduleTopology V
  exact (canonical τ₁ h₁).trans (canonical τ₂ h₂).symm

def endomorphismHomeomorph (V : Type uV)
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] :
    letI := moduleTopology ℂ (Module.End ℂ V)
    Module.End ℂ V ≃ₜ (V →L[ℂ] V) := by
  letI := moduleTopology ℂ (Module.End ℂ V)
  letI := IsModuleTopology.toContinuousAdd ℂ (Module.End ℂ V)
  letI := isModuleTopologyOfFiniteDimensional (𝕜 := ℂ) (E := V →L[ℂ] V)
  exact
    { LinearMap.toContinuousLinearMap.toEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap
        LinearMap.toContinuousLinearMap.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap
        LinearMap.toContinuousLinearMap.symm.toLinearMap }

theorem endomorphism_topology_eq_induced (V : Type uV)
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] :
    moduleTopology ℂ (Module.End ℂ V) =
      TopologicalSpace.induced
        (fun f : Module.End ℂ V => LinearMap.toContinuousLinearMap f) inferInstance := by
  let := moduleTopology ℂ (Module.End ℂ V)
  exact (endomorphismHomeomorph V).isInducing.eq_induced

end Langlands.Weil

namespace Langlands.FiniteRepresentation

variable {G : Type uG} [Group G]

theorem carrierNormed_topology_eq (A : FiniteRepresentation.{0, uG, uV} ℂ G) :
    letI := A.carrierNormedAddCommGroup
    letI := A.carrierNormedSpace
    (inferInstance : TopologicalSpace A) = moduleTopology ℂ A := by
  let := A.carrierNormedAddCommGroup
  let := A.carrierNormedSpace
  exact Weil.carrier_topology_eq_moduleTopology A

section Algebraic

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] (ρ : Representation ℂ G V) (I : Subgroup G)

theorem representation_of : (of ρ).representation = ρ := rfl

theorem representation_of_restrict :
    (of ρ).representation.comp I.subtype = ρ.comp I.subtype := rfl

theorem kernel_of : (of ρ).representation.ker = ρ.ker := rfl

theorem inertiaKernel_of :
    (of ρ).inertiaKernel I = (ρ.comp I.subtype).ker := rfl

theorem inertia_range_of :
    Set.range ((of ρ).representation.comp I.subtype) =
      Set.range (fun i : I => ρ (i : G)) := rfl

theorem hasFiniteInertiaImage_of_iff :
    (of ρ).HasFiniteInertiaImage I ↔
      (Set.range (fun i : I => ρ (i : G))).Finite := Iff.rfl

variable [TopologicalSpace G]

theorem hasOpenInertiaKernel_of_iff :
    (of ρ).HasOpenInertiaKernel I ↔ IsOpen ((ρ.comp I.subtype).ker : Set I) := Iff.rfl

end Algebraic

variable [TopologicalSpace G]
variable {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (I : Subgroup G)

theorem isContinuous_of_iff :
    (of ρ).IsContinuous ↔
      Continuous (fun g : G => (ρ g).toContinuousLinearMap) := by
  let := moduleTopology ℂ (Module.End ℂ V)
  exact (Weil.endomorphismHomeomorph V).isInducing.continuous_iff

theorem hasContinuousOrbits_of_iff :
    (of ρ).HasContinuousOrbits ↔ ∀ v : V, Continuous (fun g : G => ρ g v) := by
  unfold HasContinuousOrbits
  change (∀ v : V, @Continuous G V _ (moduleTopology ℂ V) (fun g => ρ g v)) ↔ _
  rw [← Weil.carrier_topology_eq_moduleTopology V]

theorem hasContinuousAction_of_iff :
    (of ρ).HasContinuousAction ↔ Continuous (fun x : G × V => ρ x.1 x.2) := by
  unfold HasContinuousAction
  change (@Continuous (G × V) V
    (@instTopologicalSpaceProd G V _ (moduleTopology ℂ V))
    (moduleTopology ℂ V) (fun x => ρ x.1 x.2)) ↔ _
  rw [← Weil.carrier_topology_eq_moduleTopology V]

theorem continuityClauses_of_iff :
    (of ρ).ContinuityClauses I ↔ Weil.OperatorContinuityClauses I ρ := by
  unfold ContinuityClauses Weil.OperatorContinuityClauses
  rw [isContinuous_of_iff, hasContinuousOrbits_of_iff, hasContinuousAction_of_iff,
    hasOpenInertiaKernel_of_iff, hasFiniteInertiaImage_of_iff, inertiaKernel_of]

end Langlands.FiniteRepresentation

namespace Langlands.Weil

theorem bundledRepresentationContinuity_iff :
    BundledRepresentationContinuity.{uG, uV} ↔ RepresentationContinuity.{uG, uV} := by
  constructor
  · intro h G _ _ _ I _ _ V _ _ _ ρ
    exact (FiniteRepresentation.continuityClauses_of_iff ρ I.toSubgroup).mp
      (h G I (FiniteRepresentation.of ρ))
  · intro h G _ _ _ I _ _ A
    let := A.carrierNormedAddCommGroup
    let := A.carrierNormedSpace
    have clauses : OperatorContinuityClauses I.toSubgroup A.representation := h G I A A.representation
    exact (FiniteRepresentation.continuityClauses_of_iff A.representation I.toSubgroup).mpr clauses

theorem representationContinuityCompatibility :
    RepresentationContinuityCompatibility.{uG, uV} := by
  refine ⟨carrier_topology_eq_moduleTopology, endomorphism_topology_eq_induced, ?_, ?_,
    bundledRepresentationContinuity_iff⟩
  · intro G _ A
    exact A.carrierNormed_topology_eq
  · intro G _ _ V _ _ _ ρ I
    exact ⟨FiniteRepresentation.representation_of_restrict ρ I,
      FiniteRepresentation.inertiaKernel_of ρ I,
      FiniteRepresentation.inertia_range_of ρ I,
      FiniteRepresentation.isContinuous_of_iff ρ,
      FiniteRepresentation.hasContinuousOrbits_of_iff ρ,
      FiniteRepresentation.hasContinuousAction_of_iff ρ,
      FiniteRepresentation.hasOpenInertiaKernel_of_iff ρ I,
      FiniteRepresentation.hasFiniteInertiaImage_of_iff ρ I,
      FiniteRepresentation.continuityClauses_of_iff ρ I⟩

end Langlands.Weil
