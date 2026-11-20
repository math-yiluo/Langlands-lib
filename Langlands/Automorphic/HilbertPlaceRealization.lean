import Langlands.Automorphic.HilbertPlaceGenerators
import Langlands.Representation.Archimedean.GKHilbertClosure

/-! # Applying Hilbert closure realization to a place-stable subspace -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Manifold TensorProduct

namespace Langlands.Automorphic

open Langlands.Archimedean HilbertCoefficientComparison
universe uA uE uG uK uV
attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type uA} [NormedRing A] [NormedAlgebra ℝ A]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace A G]
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {K : Type uK} [Group K] [TopologicalSpace K]
  (π : G →* (E →L[ℂ] E)) (j : V →ₗ[ℂ] E) (iK : K →* G)
  (κ : Representation ℂ K V) (d : (ℂ ⊗[ℝ] A) →ₗ⁅ℂ⁆ Module.End ℂ V)
  (hplace : PlaceClosureCompatibility π j iK κ d) (W : Submodule ℂ V)
  (hW : PlaceComponent.IsStable κ d W)

omit [TopologicalSpace G] [ChartedSpace A G] [TopologicalSpace K] in
include hplace hW in
/-- The closure of the image of the restricted embedding is the closure in
place compatibility. -/
theorem placeRangeClosure_stable
    (g : G) (x : (LinearMap.range (j.comp W.subtype)).topologicalClosure) :
    π g x ∈ (LinearMap.range (j.comp W.subtype)).topologicalClosure := by
  have h : (LinearMap.range (j.comp W.subtype)).topologicalClosure = (W.map j).topologicalClosure := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hx : (x : E) ∈ (W.map j).topologicalClosure := h ▸ x.property
  exact (congrArg (fun M : Submodule ℂ E => π g x ∈ M) h).mpr
    (hplace.2 W hW g x hx)

/-- The Hilbert representation on the closure of the image of a local algebraic subspace. -/
def placeClosureRepresentation : G →*
    ((LinearMap.range (j.comp W.subtype)).topologicalClosure →L[ℂ]
      (LinearMap.range (j.comp W.subtype)).topologicalClosure) :=
  invariantSubmoduleRepresentation π _ (placeRangeClosure_stable π j iK κ d hplace W hW)

/-- The Hilbert closure realizes the restricted original compact and Lie module. -/
def IsPlaceHilbertRealization : Prop :=
  IsGKHilbertRealization iK (PlaceComponent.restrictCompact hW) (PlaceComponent.restrictLie hW)
    (placeClosureRepresentation π j iK κ d hplace W hW) (rangeClosureEmbedding (j.comp W.subtype))

/-- The given ambient action realizes the algebraic place subspace on its image closure. -/
def HasPlaceHilbertRealization : Prop :=
  ∃ (hplace : PlaceClosureCompatibility π j iK κ d) (hW : PlaceComponent.IsStable κ d W),
    IsPlaceHilbertRealization π j iK κ d hplace W hW

variable [CompleteSpace E] [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K]
  [BorelSpace K] [SecondCountableTopology K]

/-- All the closure realization data follow from the original place action
and the original subspace's admissibility and irreducibility. -/
theorem isPlaceHilbertRealization_of_ambient
    (hiK : Continuous iK) (hj : Function.Injective j)
    (hcont : IsContinuousRepresentation π)
    (hinner : ∀ g x y, Inner.inner ℂ (π g x) (π g y) = Inner.inner ℂ x y)
    (hfin : ∀ v, FiniteVectors.IsFiniteVector κ v)
    (hs : ∀ v, Langlands.Archimedean.IsSmoothVector 𝓘(ℝ, A) π (j v))
    (hd : RealGeneratorCompatibility π j (fun X v => d (1 ⊗ₜ[ℝ] X) v) id)
    (hirr : PlaceComponent.IsIrreducible κ d W) (hadm : PlaceComponent.IsAdmissible κ W) :
    IsPlaceHilbertRealization π j iK κ d hplace W hW := by
  exact gkHilbertClosure A G K iK hiK W (PlaceComponent.restrictCompact hW)
    (PlaceComponent.restrictLie hW) E π (j.comp W.subtype)
    (placeRangeClosure_stable π j iK κ d hplace W hW)
    (PlaceComponent.isIrreducibleGKModule_restrict hirr)
    (PlaceComponent.isAdmissibleGKModule_restrict hW hadm)
    (fun v => PlaceComponent.isFiniteVector_restrictCompact hW v (hfin v))
    (hj.comp Subtype.val_injective) hcont hinner (fun k v => (hplace.1 k v).symm)
    (fun v => hs v) (fun X v => hd X v)

end Langlands.Automorphic
