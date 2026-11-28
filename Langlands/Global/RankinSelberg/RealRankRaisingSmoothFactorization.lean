import Langlands.Global.RankinSelberg.RealRankRaisingKernel
import Langlands.Representation.Archimedean.SmoothVectorSubgroupFactorization
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Smooth-vector factorization in the real rank-raising coordinates -/

noncomputable section

open Filter MeasureTheory
open scoped ContDiff Manifold SchwartzMap Matrix.Norms.Operator NNReal ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealRankRaisingIntegral

open Langlands.Archimedean Langlands.Archimedean.DerivativeSmoothVectors
open Langlands.GeneralLinear Langlands.HarmonicAnalysis
open Langlands.RankinSelberg (rectangularMeasure)
open ArchimedeanLocal

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (lowerTriangularSubgroup n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (lowerTriangularSubgroup n ℝ) := ⟨rfl⟩
private local instance (r : ℕ) : MeasurableSpace (rankRaisingSubgroup r) := borel _
private local instance (r : ℕ) : BorelSpace (rankRaisingSubgroup r) := ⟨rfl⟩

local notation "B" => lowerTriangularSubgroup 1 ℝ
local notation "X" => fun r => Matrix (Fin 1) (Fin (r + 1)) ℝ
local notation "P" => fun r => X r × B
local notation "W" => fun r => X r × ℝ
local notation "A" => fun r => Matrix (Fin (r + 1 + 1)) (Fin (r + 1 + 1)) ℝ
local notation "G" => fun r => Langlands.GeneralLinear (r + 1 + 1) ℝ
local notation "H" => rankRaisingSubgroup
local notation "chart" => rankRaisingHomeomorph
local notation "I" => fun r => 𝓘(ℝ, A r)

/-- The right-invariant measure written in the row and trailing coordinates. -/
def rankRaisingCoordinateMeasure (r : ℕ) (ν : AdditiveHaarMeasure ℝ) (ρ : Measure B) : Measure (P r) :=
  (rectangularMeasure ν 1 (r + 1)).prod (ρ.withDensity fun h => (trailingHeight h : ℝ≥0∞))

private theorem continuous_relativeDensity (r : ℕ) : Continuous (rankRaisingLeftRelativeDensity r) := by
  have hval : Continuous (fun h : B => h.val.val) := Units.continuous_val.comp continuous_subtype_val
  have h : Continuous trailingHeight := continuous_nnnorm.comp hval.matrix_det
  apply Continuous.comp _ (continuous_snd.comp (chart r).symm.continuous)
  exact (h.pow _).inv₀ fun k => pow_ne_zero _ (nnnorm_ne_zero_iff.mpr (determinant k.val).ne_zero)

/-- The smooth orbit average along a homomorphism, in the compensating row coordinates. -/
def mappedRankRaisingAverageIntegrand {r : ℕ} {C E : Type*}
    [NormedRing C] [NormedAlgebra ℝ C] [CompleteSpace C]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (σ : G r →* Cˣ) (R : Cˣ →* (E →L[ℂ] E)) (φ : 𝓢(W r, ℂ))
    (L : DerivativeSmoothVectors 𝓘(ℝ, C) R →L[ℂ] ℂ) (w : DerivativeSmoothVectors 𝓘(ℝ, C) R)
    (p : P r) : ℂ :=
  φ (p.1, p.2.val.val.det) * L (representation 𝓘(ℝ, C) R (σ (rankRaisingSmoothingMatrix p)) w)

/-- Genuine smooth vectors factor through a mapped rank-raising subgroup. The kernels are
compactly supported Schwartz functions of the full bottom row. -/
def RealRankRaisingMappedSmoothFactorizationStatement : Prop :=
  ∀ (r : ℕ) (ν : AdditiveHaarMeasure ℝ) (ρ : Measure B) [SigmaFinite ρ] [ρ.IsHaarMeasure]
    [ρ.IsMulRightInvariant] (C : Type*) [NormedRing C] [NormedAlgebra ℝ C] [CompleteSpace C]
    [FiniteDimensional ℝ C] (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (σ : G r →* Cˣ) (j : A r →ₗ[ℝ] C) (R : Cˣ →* (E →L[ℂ] E)),
    let D := DerivativeSmoothVectors 𝓘(ℝ, C) R
    IsContinuousRepresentation R → Continuous σ →
    (∀ Y : A r, σ (Langlands.LinearLieGroup.expUnit (A r) Y) =
      Langlands.LinearLieGroup.expUnit C (j Y)) → ∀ v : D,
    ∃ (m : ℕ) (w : Fin m → D) (φ : Fin m → 𝓢(W r, ℂ)),
      (∀ i, HasCompactSupport (φ i) ∧ tsupport (φ i) ⊆ {p : W r | p.2 ≠ 0}) ∧
      ∀ L : D →L[ℂ] ℂ,
        (∀ i, Integrable (mappedRankRaisingAverageIntegrand σ R (φ i) L (w i))
          (rankRaisingCoordinateMeasure r ν ρ)) ∧
        L v = ∑ i, ∫ p, mappedRankRaisingAverageIntegrand σ R (φ i) L (w i) p
          ∂rankRaisingCoordinateMeasure r ν ρ

set_option maxHeartbeats 600000 in
theorem realRankRaisingMappedSmoothFactorization : RealRankRaisingMappedSmoothFactorizationStatement := by
  intro r ν ρ _ _ _ C _ _ _ _ E _ _ _ σ j R D hR hσ hExp v
  obtain ⟨hLeft, _, hRight, _, hRatio⟩ := realRankRaisingHaar r ν ρ
  let μL := rankRaisingLeftHaar r ν ρ
  let μR := rankRaisingRightHaar r ν ρ
  let μ := rankRaisingCoordinateMeasure r ν ρ
  let : μL.IsHaarMeasure := hLeft
  let : IsFiniteMeasureOnCompacts μR := hRight
  let σH := σ.comp (H r).subtype
  let jH := j.comp (rankRaisingLie r).subtype
  have hExpH (t : ℝ) (Y : rankRaisingLie r) : σH ((rankRaisingExpLie r).expG (t • Y)) =
      Langlands.LinearLieGroup.expUnit C (t • jH Y) := by
    change σ (Langlands.LinearLieGroup.expUnit (A r) (t • (Y : A r))) =
      Langlands.LinearLieGroup.expUnit C (t • j (Y : A r))
    rw [hExp, map_smul]
  obtain ⟨m, w, K, hK, hEq⟩ := smoothVectorMappedSubgroupFactorization (A r) C E R (H r)
    (rankRaisingLie r) (rankRaisingExpLie r) σH jH μL hR (hσ.comp continuous_subtype_val) hExpH
    Set.univ Filter.univ_mem v
  choose φ hC hS hφ using fun i => realRankRaisingKernel r (K i) (hK i).1 (hK i).2.1
  let := (rankRaisingExpLie r).chartedSpace
  refine ⟨m, w, φ, fun i => ⟨hC i, hS i⟩, fun L => ?_⟩
  let F (i : Fin m) (g : H r) := K i g * L (representation 𝓘(ℝ, C) R (σ g.val) (w i))
  let weight := rankRaisingLeftRelativeDensity r
  let V (i : Fin m) (g : H r) := ((weight g : ℝ) : ℂ) * F i g
  let V' (i : Fin m) := mappedRankRaisingAverageIntegrand σ R (φ i) L (w i)
  have hV (i : Fin m) : Continuous (V i) := by
    have hO : Continuous (fun g : H r => L (representation 𝓘(ℝ, C) R (σ g.val) (w i))) :=
      L.continuous.comp ((continuous_representation_units R hR).comp
        ((hσ.comp continuous_subtype_val).prodMk continuous_const))
    exact (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (continuous_relativeDensity r))).mul
      (((hK i).1.continuous).mul hO)
  have hComp (i : Fin m) : HasCompactSupport (V i) := ((hK i).2.1.mul_right).mul_left
  have hVeq (i : Fin m) : V i ∘ chart r = V' i := by
    funext p
    change ((weight (chart r p) : ℝ) : ℂ) * (K i (chart r p) *
      L (representation 𝓘(ℝ, C) R (σ (chart r p).val) (w i))) = _
    rw [rankRaisingHomeomorph_apply_val]
    unfold V' mappedRankRaisingAverageIntegrand
    rw [hφ i p]
    ring
  have hμ : μR = μ.map (chart r) := rfl
  have hInt (i : Fin m) : Integrable (V' i) μ := by
    rw [← hVeq]
    have hv : Integrable (V i) μR := (hV i).integrable_of_hasCompactSupport (hComp i)
    exact (integrable_map_measure (hV i).aestronglyMeasurable
      (chart r).continuous.measurable.aemeasurable).mp hv
  refine ⟨hInt, (hEq L).trans (Finset.sum_congr rfl fun i _ => ?_)⟩
  change (∫ g, F i g ∂μL) = ∫ p, V' i p ∂μ
  calc
    _ = ∫ g, V i g ∂μR := by
      rw [show μL = μR.withDensity (fun g => (weight g : ℝ≥0∞)) from hRatio.symm,
        integral_withDensity_eq_integral_smul (continuous_relativeDensity r).measurable]
      simp only [V, weight, NNReal.smul_def, Complex.real_smul]
    _ = _ := by
      rw [hμ, integral_map (chart r).continuous.measurable.aemeasurable (hV i).aestronglyMeasurable]
      exact congrArg (fun F : P r → ℂ => ∫ p, F p ∂μ) (hVeq i)

/-- The smooth orbit average integrand in the compensating row coordinates. -/
def rankRaisingAverageIntegrand {r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (R : G r →* (E →L[ℂ] E)) (φ : 𝓢(W r, ℂ))
    (L : DerivativeSmoothVectors (I r) R →L[ℂ] ℂ) (w : DerivativeSmoothVectors (I r) R)
    (p : P r) : ℂ :=
  mappedRankRaisingAverageIntegrand (MonoidHom.id _) R φ L w p

/-- Genuine smooth vectors factor as finite averages in the actual rank-raising coordinates.
The kernels are compactly supported Schwartz functions of the full bottom row. -/
def RealRankRaisingSmoothFactorizationStatement : Prop :=
  ∀ (r : ℕ) (ν : AdditiveHaarMeasure ℝ) (ρ : Measure B) [SigmaFinite ρ] [ρ.IsHaarMeasure]
    [ρ.IsMulRightInvariant] (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (R : G r →* (E →L[ℂ] E)),
    let D := DerivativeSmoothVectors (I r) R
    IsContinuousRepresentation R → ∀ v : D,
    ∃ (m : ℕ) (w : Fin m → D) (φ : Fin m → 𝓢(W r, ℂ)),
      (∀ i, HasCompactSupport (φ i) ∧ tsupport (φ i) ⊆ {p : W r | p.2 ≠ 0}) ∧
      ∀ L : D →L[ℂ] ℂ,
        (∀ i, Integrable (rankRaisingAverageIntegrand R (φ i) L (w i))
          (rankRaisingCoordinateMeasure r ν ρ)) ∧
        L v = ∑ i, ∫ p, rankRaisingAverageIntegrand R (φ i) L (w i) p
          ∂rankRaisingCoordinateMeasure r ν ρ

set_option maxHeartbeats 600000 in
theorem realRankRaisingSmoothFactorization : RealRankRaisingSmoothFactorizationStatement := by
  intro r ν ρ _ _ _ E _ _ _ R D hR v
  exact realRankRaisingMappedSmoothFactorization r ν ρ (A r) E (MonoidHom.id _)
    (LinearMap.id) R hR continuous_id (fun _ => rfl) v

end Langlands.Global.RankinSelbergGlobal.RealRankRaisingIntegral
