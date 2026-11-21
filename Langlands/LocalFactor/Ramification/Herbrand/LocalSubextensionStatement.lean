import Langlands.LocalFactor.Ramification.Herbrand.GeneralAbsolute
import Langlands.LocalFactor.Ramification.Herbrand.GeneralSubextension

/-!
# Herbrand's subgroup formula in either characteristic

The finite formula uses a single local-field realization. The relative
inverse Herbrand function for a finite subextension is evaluated in the
normal closure, and the absolute formula uses a common separable closure.
-/

namespace Langlands.Ramification.Local

universe u₀ uK uE uM uΩ

/-- For every real `u`, an `E`-automorphism `σ` of `M` has `σ.restrictScalars K`
in the upper group of `M/K` at `u` exactly when `σ` is in the upper group of
`M/E` at `φ_{M/E}(ψ_{M/K}(u))`, all computed in one realization `T` of `M/K₀`. -/
def FiniteHerbrandSubgroupFormula : Prop :=
  ∀ (K₀ : Type u₀) [Field K₀] [ValuativeRel K₀] [TopologicalSpace K₀]
    (K : Type uK) [Field K] [Algebra K₀ K]
    (E : Type uE) [Field E] [Algebra K E] [Algebra K₀ E]
    (M : Type uM) [Field M] [Algebra K₀ M] [FiniteDimensional K₀ M]
    [Algebra K M] [Algebra E M] [IsScalarTower K E M]
    [IsScalarTower K₀ K M] [IsScalarTower K₀ E M]
    (T : LocalField.TopologicalData K₀ M) (u : ℝ) (σ : M ≃ₐ[E] M),
    σ.restrictScalars K ∈ upperRamificationGroup T K u ↔
      σ ∈ upperRamificationGroup T E (herbrandPhi T E (herbrandPsi T K u))

/-- Every finite Galois intermediate field `M` of `Ω/K` containing `E` gives the
same relative index `φ_{M/E} ∘ ψ_{M/K}` as the chosen normal closure of `E/K`,
at every real argument. -/
def RelativeHerbrandPsiIndependence : Prop :=
  ∀ (K₀ : Type u₀) [NontriviallyNormedField K₀] [IsUltrametricDist K₀]
    [CompleteSpace K₀] [ValuativeRel K₀] [LocallyCompactSpace K₀]
    (K : Type uK) [Field K] [Algebra K₀ K] [FiniteDimensional K₀ K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    [Algebra K₀ Ω] [IsScalarTower K₀ K Ω]
    (hbase : ∀ a b : K₀, ‖a‖ ≤ ‖b‖ ↔ ValuativeRel.vle a b)
    (E : IntermediateField K Ω) [FiniteDimensional K E]
    (M : FiniteGaloisIntermediateField K Ω)
    (h : ∀ x : E, algebraMap E Ω x ∈ M.toIntermediateField) (u : ℝ),
    haveI : IsScalarTower K₀ E Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
    relativeHerbrandPsi K₀ K Ω hbase E u = relativeIndex K₀ K hbase M h u

/-- For `u ≥ -1`, the upper filtration of `K` on the automorphisms of `Ω` fixing `E`
is the upper filtration of `E` at the relative inverse Herbrand index `ψ_{E/K}(u)`. -/
def AbsoluteHerbrandSubgroupFormula : Prop :=
  ∀ (K₀ : Type u₀) [NontriviallyNormedField K₀] [IsUltrametricDist K₀]
    [CompleteSpace K₀] [ValuativeRel K₀] [LocallyCompactSpace K₀]
    (K : Type uK) [Field K] [Algebra K₀ K] [FiniteDimensional K₀ K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    [Algebra K₀ Ω] [IsScalarTower K₀ K Ω]
    (hbase : ∀ a b : K₀, ‖a‖ ≤ ‖b‖ ↔ ValuativeRel.vle a b)
    (E : IntermediateField K Ω) [FiniteDimensional K E] (u : ℝ),
    -1 ≤ u → ∀ τ : Ω ≃ₐ[E] Ω,
      haveI : FiniteDimensional K₀ E := FiniteDimensional.trans K₀ K E
      haveI : IsScalarTower K₀ E Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
      haveI : IsSepClosure E Ω :=
        ⟨IsSepClosure.sep_closed K, (IsGalois.tower_top_of_isGalois K E Ω).to_isSeparable⟩
      τ.restrictScalars K ∈ absoluteUpperRamificationGroup K₀ K Ω hbase u ↔
        τ ∈ absoluteUpperRamificationGroup K₀ E Ω hbase
          (relativeHerbrandPsi K₀ K Ω hbase E u)

end Langlands.Ramification.Local
