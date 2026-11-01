import Langlands.Representation.RankinSelberg.AdjacentRankModelConvergenceProof
import Langlands.Representation.RankinSelberg.CharacterChange

/-!
# The linear adjacent-rank integral map

The literal integral on the whole algebraic tensor product is a linear map.
Its image is the span of the pure-tensor integrals. The partial Fourier
equivalence acts on this whole tensor product, and its conjugacy relation
is compatible with the literal integral.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker TensorProduct

universe uF uV

section Fourier

variable {K : Type uF} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K] [LocallyCompactSpace K] [T2Space K]
  [TotallyDisconnectedSpace K]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter K) (ν : AdditiveHaarMeasure K) (hself : IsSelfDual ψ ν)
  {r : ℕ} (σ : Representation ℂ (GeneralLinear (r + 1) K) V)
  (ℓ : glFunctionals ψ r σ)

/-- The supplied last-column Fourier equivalence on the Schwartz tensor factor. -/
def adjacentRankFourierEquiv :
    adjacentRankTestSpace ψ σ ℓ ≃ₗ[ℂ] adjacentRankTestSpace ψ σ ℓ :=
  TensorProduct.congr (partialFourierEquiv ψ ν (r + 1) hself) (LinearEquiv.refl ℂ _)

@[simp] theorem adjacentRankFourierEquiv_tmul
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) K))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule) :
    adjacentRankFourierEquiv ψ ν hself σ ℓ (Φ ⊗ₜ W) =
      partialFourierEquiv ψ ν (r + 1) hself Φ ⊗ₜ W := rfl

/-- The untranslated right action, before conjugation by partial Fourier. -/
def adjacentRankSchwartzAction (g : GeneralLinear (r + 2) K) :
    Module.End ℂ (adjacentRankTestSpace ψ σ ℓ) :=
  TensorProduct.map (rectangularSchwartzRepresentation g) LinearMap.id

omit [MeasurableSpace K] [BorelSpace K] [LocallyCompactSpace K] [T2Space K]
  [TotallyDisconnectedSpace K] in
@[simp] theorem adjacentRankSchwartzAction_tmul (g : GeneralLinear (r + 2) K)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) K))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule) :
    adjacentRankSchwartzAction ψ σ ℓ g (Φ ⊗ₜ W) = rectangularTranslate g Φ ⊗ₜ W :=
  rfl

/-- The defining JPSS Fourier conjugacy on every finite algebraic tensor. -/
theorem adjacentRankFourierEquiv_intertwine (g : GeneralLinear (r + 2) K)
    (Ψ : adjacentRankTestSpace ψ σ ℓ) :
    adjacentRankRho0 ψ ν hself σ ℓ g (adjacentRankFourierEquiv ψ ν hself σ ℓ Ψ) =
      adjacentRankFourierEquiv ψ ν hself σ ℓ (adjacentRankSchwartzAction ψ σ ℓ g Ψ) := by
  induction Ψ using adjacentRankTestSpace_induction ψ σ ℓ with
  | tmul Φ W =>
    simp only [adjacentRankFourierEquiv_tmul, adjacentRankRho0_tmul,
      adjacentRankSchwartzAction_tmul, rectangularRho0_intertwine]
  | add Ψ₁ Ψ₂ h₁ h₂ =>
    simp only [map_add, h₁, h₂]

end Fourier

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance : MeasurableSpace F.Carrier := borel _
local instance : BorelSpace F.Carrier := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
  (hself : IsSelfDual ψ ν) {r : ℕ}
  (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
  (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F.Carrier)

/-- Smoothness suffices for convergence of the entire finite tensor integral. -/
theorem adjacentRankModelConverges_of_isSmooth (hσ : IsSmooth σ)
    (Ψ : adjacentRankTestSpace ψ σ ℓ) (g : GeneralLinear (r + 2) F.Carrier) :
    AdjacentRankModelConverges F ψ ν hself σ ℓ χ Ψ g := by
  induction Ψ using adjacentRankTestSpace_induction ψ σ ℓ with
  | tmul Φ W =>
    exact adjacentRankModelConverges_tmul_of_isSmooth F ψ ν hself r σ hσ ℓ χ Φ W g
  | add Ψ₁ Ψ₂ h₁ h₂ =>
    exact RankinSelberg.AdjacentRankModelConverges.add h₁ h₂

/-- The literal integral as a linear map on the whole algebraic test space.
The smoothness proof supplies additivity via unconditional convergence. -/
def adjacentRankModelMap (hσ : IsSmooth σ) :
    adjacentRankTestSpace ψ σ ℓ →ₗ[ℂ] (GeneralLinear (r + 2) F.Carrier → ℂ) where
  toFun Ψ := adjacentRankModelIntegral F ψ ν hself σ ℓ χ Ψ
  map_add' Ψ₁ Ψ₂ := by
    funext g
    exact RankinSelberg.adjacentRankModelIntegral_add
      (adjacentRankModelConverges_of_isSmooth F ψ ν hself σ ℓ χ hσ Ψ₁ g)
      (adjacentRankModelConverges_of_isSmooth F ψ ν hself σ ℓ χ hσ Ψ₂ g)
  map_smul' c Ψ := by
    funext g
    exact RankinSelberg.adjacentRankModelIntegral_smul c Ψ

@[simp] theorem adjacentRankModelMap_apply (hσ : IsSmooth σ)
    (Ψ : adjacentRankTestSpace ψ σ ℓ) (g : GeneralLinear (r + 2) F.Carrier) :
    adjacentRankModelMap F ψ ν hself σ ℓ χ hσ Ψ g =
      adjacentRankModelIntegral F ψ ν hself σ ℓ χ Ψ g := rfl

/-- Every whole-function integral is a finite sum of pure-tensor integrals,
with the same tests working simultaneously at every ambient group element. -/
theorem adjacentRankModelMap_exists_sum_tmul (hσ : IsSmooth σ)
    (Ψ : adjacentRankTestSpace ψ σ ℓ) :
    ∃ (n : ℕ)
      (Φ : Fin n → SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier))
      (W : Fin n → (glCoefficientModel ψ r σ ℓ).toSubmodule),
      adjacentRankModelMap F ψ ν hself σ ℓ χ hσ Ψ =
        ∑ j, adjacentRankModelMap F ψ ν hself σ ℓ χ hσ (Φ j ⊗ₜ W j) := by
  obtain ⟨n, Φ, W, hΨ⟩ := adjacentRankTestSpace_exists_sum_tmul ψ σ ℓ Ψ
  refine ⟨n, Φ, W, ?_⟩
  rw [hΨ, map_sum]

/-- The whole integral image is exactly the complex linear span of the
pure-tensor images; no pointwise choice of a tensor is used. -/
theorem range_adjacentRankModelMap (hσ : IsSmooth σ) :
    LinearMap.range (adjacentRankModelMap F ψ ν hself σ ℓ χ hσ) =
      Submodule.span ℂ (Set.range (fun v :
        SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier) ×
          (glCoefficientModel ψ r σ ℓ).toSubmodule =>
        adjacentRankModelMap F ψ ν hself σ ℓ χ hσ (v.1 ⊗ₜ v.2))) := by
  apply le_antisymm
  · rintro _ ⟨Ψ, rfl⟩
    obtain ⟨n, Φ, W, hΨ⟩ := adjacentRankModelMap_exists_sum_tmul F ψ ν hself σ ℓ χ hσ Ψ
    rw [hΨ]
    exact Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨(Φ j, W j), rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨Φ, W⟩, rfl⟩
    exact ⟨Φ ⊗ₜ W, rfl⟩

/-- Partial Fourier on all test tensors leaves the whole integral image unchanged. -/
theorem range_adjacentRankModelMap_fourier (hσ : IsSmooth σ) :
    Set.range (fun Ψ => adjacentRankModelMap F ψ ν hself σ ℓ χ hσ
      (adjacentRankFourierEquiv ψ ν hself σ ℓ Ψ)) =
      Set.range (adjacentRankModelMap F ψ ν hself σ ℓ χ hσ) := by
  ext f
  constructor
  · rintro ⟨Ψ, rfl⟩
    exact ⟨adjacentRankFourierEquiv ψ ν hself σ ℓ Ψ, rfl⟩
  · rintro ⟨Ψ, rfl⟩
    exact ⟨(adjacentRankFourierEquiv ψ ν hself σ ℓ).symm Ψ,
      congrArg (adjacentRankModelMap F ψ ν hself σ ℓ χ hσ)
        ((adjacentRankFourierEquiv ψ ν hself σ ℓ).apply_symm_apply Ψ)⟩

/-- Right translation of the ambient variable agrees with `ρ₀` on the
tensor and the prescribed outer character and determinant factors. -/
theorem adjacentRankModelIntegral_mul (Ψ : adjacentRankTestSpace ψ σ ℓ)
    (g k : GeneralLinear (r + 2) F.Carrier) :
    adjacentRankModelIntegral F ψ ν hself σ ℓ χ Ψ (g * k) =
      (χ (GeneralLinear.determinant k) : ℂ) *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
          k (((r + 1 : ℕ) : ℂ) / 2) *
        adjacentRankModelIntegral F ψ ν hself σ ℓ χ
          (adjacentRankRho0 ψ ν hself σ ℓ k Ψ) g := by
  unfold adjacentRankModelIntegral RankinSelberg.adjacentRankModelIntegral
  simp only [map_mul, Units.val_mul, determinantWeight_mul,
    RankinSelberg.adjacentRankModelIntegrand, Module.End.mul_apply]
  ring

end Padic

end Langlands.RankinSelberg
