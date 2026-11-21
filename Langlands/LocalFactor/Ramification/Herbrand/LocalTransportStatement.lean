import Langlands.LocalFactor.Ramification.Herbrand.GeneralTransport

/-!
# Transport of the Herbrand filtration in either characteristic

Naturality under isomorphism of the finite filtration with supplied
local-field realizations and of the filtration in a common ambient field.
-/

namespace Langlands.Ramification.Local

universe u₀ uK uL₁ uL₂

/-- Transport of the finite filtration, group orders and Herbrand functions
along an isomorphism over `K` and a common valued base `K₀`. -/
def FiniteHerbrandTransport : Prop :=
  ∀ (K₀ : Type u₀) [Field K₀] [ValuativeRel K₀] [TopologicalSpace K₀]
    (K : Type uK) [Field K] [Algebra K₀ K]
    (L₁ : Type uL₁) [Field L₁] [Algebra K₀ L₁] [FiniteDimensional K₀ L₁]
    [Algebra K L₁] [IsScalarTower K₀ K L₁]
    (L₂ : Type uL₂) [Field L₂] [Algebra K₀ L₂] [FiniteDimensional K₀ L₂]
    [Algebra K L₂] [IsScalarTower K₀ K L₂]
    (T₁ : LocalField.TopologicalData K₀ L₁) (T₂ : LocalField.TopologicalData K₀ L₂)
    (f : L₁ ≃ₐ[K] L₂),
    (∀ (i : ℕ) (σ : L₁ ≃ₐ[K] L₁),
      f.autCongr σ ∈ lowerRamificationGroup T₂ K i ↔
        σ ∈ lowerRamificationGroup T₁ K i) ∧
    (∀ (i : ℤ) (σ : L₁ ≃ₐ[K] L₁),
      f.autCongr σ ∈ lowerRamificationGroupInt T₂ K i ↔
        σ ∈ lowerRamificationGroupInt T₁ K i) ∧
    (∀ i : ℕ, lowerGroupOrder T₂ K i = lowerGroupOrder T₁ K i) ∧
    (∀ u : ℝ, herbrandPhi T₂ K u = herbrandPhi T₁ K u) ∧
    (∀ u : ℝ, herbrandPsi T₂ K u = herbrandPsi T₁ K u) ∧
    (∀ (u : ℝ) (σ : L₁ ≃ₐ[K] L₁),
      f.autCongr σ ∈ upperRamificationGroup T₂ K u ↔
        σ ∈ upperRamificationGroup T₁ K u)

/-- Transport of the ambient upper filtration, which is the absolute
filtration when the ambient field is a separable closure. -/
def AmbientUpperRamificationTransport : Prop :=
  ∀ (K₀ : Type u₀) [NontriviallyNormedField K₀] [IsUltrametricDist K₀]
    [CompleteSpace K₀] [ValuativeRel K₀] [LocallyCompactSpace K₀]
    (K : Type uK) [Field K] [Algebra K₀ K] [FiniteDimensional K₀ K]
    (Ω₁ : Type uL₁) [Field Ω₁] [Algebra K Ω₁] [Algebra K₀ Ω₁]
    [IsScalarTower K₀ K Ω₁]
    (Ω₂ : Type uL₂) [Field Ω₂] [Algebra K Ω₂] [Algebra K₀ Ω₂]
    [IsScalarTower K₀ K Ω₂]
    (hbase : ∀ a b : K₀, ‖a‖ ≤ ‖b‖ ↔ ValuativeRel.vle a b)
    (f : Ω₁ ≃ₐ[K] Ω₂) (u : ℝ) (σ : Ω₁ ≃ₐ[K] Ω₁),
    f.autCongr σ ∈ upperGroupIn K₀ K Ω₂ hbase u ↔
      σ ∈ upperGroupIn K₀ K Ω₁ hbase u

end Langlands.Ramification.Local
