import Langlands.Weil.Representation.ContinuityBridgeDefinitions

/-!
# Exact targets for the bundled continuity presentation

These are compatibility propositions. Neither formulation of the five
substantive continuity equivalences is asserted as a theorem here.
-/

universe uG uV

namespace Langlands.Weil

/-- Uniqueness of the finite-dimensional Hausdorff complex vector topology.
This also makes all compatible norm and coordinate choices topologically
independent, including for the zero vector space. -/
def CarrierTopologyComparison : Prop :=
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℂ V] [T2Space V],
    (inferInstance : TopologicalSpace V) = moduleTopology ℂ V

/-- The canonical endomorphism topology is the operator topology transported
along the actual linear-map to continuous-linear-map equivalence. -/
def EndomorphismTopologyComparison : Prop :=
  ∀ (V : Type uV) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V],
    moduleTopology ℂ (Module.End ℂ V) =
      TopologicalSpace.induced
        (fun f : Module.End ℂ V => LinearMap.toContinuousLinearMap f) inferInstance

/-- The explicitly constructed norm on each bundled carrier has its canonical
complex module topology. No topology equivalence is supplied as input. -/
def ChosenCarrierTopologyComparison : Prop :=
  ∀ (G : Type uG) [Group G] (A : FiniteRepresentation.{0, uG, uV} ℂ G),
    letI := A.carrierNormedAddCommGroup
    letI := A.carrierNormedSpace
    (inferInstance : TopologicalSpace A) = moduleTopology ℂ A

/-- The individual predicates, actual restrictions, kernels, ranges, and whole
five-clause expressions correspond under `FiniteRepresentation.of`. -/
def RepresentationPredicateComparison : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G]
    (V : Type uV) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (I : Subgroup G),
    let A := FiniteRepresentation.of ρ
    (A.representation.comp I.subtype = ρ.comp I.subtype) ∧
    (A.inertiaKernel I = (ρ.comp I.subtype).ker) ∧
    (Set.range (A.representation.comp I.subtype) =
      Set.range (fun i : I => ρ (i : G))) ∧
    (A.IsContinuous ↔ Continuous (fun g : G => (ρ g).toContinuousLinearMap)) ∧
    (A.HasContinuousOrbits ↔ ∀ v : V, Continuous (fun g : G => ρ g v)) ∧
    (A.HasContinuousAction ↔ Continuous (fun x : G × V => ρ x.1 x.2)) ∧
    (A.HasOpenInertiaKernel I ↔ IsOpen ((ρ.comp I.subtype).ker : Set I)) ∧
    (A.HasFiniteInertiaImage I ↔ (Set.range (fun i : I => ρ (i : G))).Finite) ∧
    (A.ContinuityClauses I ↔ OperatorContinuityClauses I ρ)

/-- The complete compatibility target, including both directions of the
universally quantified family. It does not assert either family itself. -/
def RepresentationContinuityCompatibility : Prop :=
  CarrierTopologyComparison.{uV} ∧
  EndomorphismTopologyComparison.{uV} ∧
  ChosenCarrierTopologyComparison.{uG, uV} ∧
  RepresentationPredicateComparison.{uG, uV} ∧
  (BundledRepresentationContinuity.{uG, uV} ↔ RepresentationContinuity.{uG, uV})

end Langlands.Weil
