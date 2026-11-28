import Langlands.Representation.Archimedean.CompactFiniteSmoothness
import Langlands.Representation.Archimedean.OrthogonalGroupAveraging
import Langlands.Representation.Archimedean.RealSmoothCompactFiniteDensity

/-! # Lifting compact-finite vectors through smooth quotients -/

noncomputable section

open Langlands.CompactRepresentativeWeights MeasureTheory Set
open scoped Matrix Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open DerivativeSmoothVectors

universe uE uF

variable {n : ℕ}

local notation:max "G" rank:max => Langlands.GeneralLinear rank ℝ
local notation:max "K" rank:max => Matrix.unitaryGroup (Fin rank) ℝ
local notation:max "I" rank:max => matrixModel ℝ rank
local notation:max "D" rank:max R:max => DerivativeSmoothVectors (I rank) R

private abbrev smoothOrthogonalAction (rank : ℕ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (R : G rank →* (E →L[ℂ] E)) : Representation ℂ (K rank) (D rank R) :=
  (representation (I rank) R).comp Unitary.toUnits

local notation:max "κ" rank:max R:max => smoothOrthogonalAction rank R

private theorem continuous_subMatrix_smooth {E : Type uE} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (R : G n →* (E →L[ℂ] E))
    (hR : IsContinuousRepresentation R) (W : Subrepresentation (κ n R))
    [FiniteDimensional ℂ W.toSubmodule] : Continuous (Langlands.KFiniteDual.subMatrix W) := by
  let p := derivativeCLM (I n) R []
  let J := p.toLinearMap.comp W.toSubmodule.subtype
  have hJ : Function.Injective J :=
    (show Function.Injective p from fun _ _ h => (toSmooth (I n) R).injective (Subtype.ext h)).comp
      Subtype.val_injective
  let e := LinearEquiv.ofInjective J hJ
  let b := Module.finBasis ℂ W.toSubmodule
  refine continuous_matrix fun i j => ?_
  let c := ((b.coord i).comp e.symm.toLinearMap).toContinuousLinearMap
  let f (k : K n) : J.range := e (W.toRepresentation k (b j))
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact p.continuous.comp ((continuous_representation_units R hR).comp
      (continuous_unitary_toUnits.prodMk continuous_const))
  exact (c.continuous.comp hf).congr fun k => by
    change (b.coord i) (e.symm (e (W.toRepresentation k (b j)))) = _
    rw [LinearEquiv.symm_apply_apply, Langlands.KFiniteDual.subMatrix_apply, Module.Basis.coord_apply]

private theorem compactInverseCoordinateWeight_mem_finiteWeights
    {K₀ : Type*} [Group K₀] [TopologicalSpace K₀] [IsTopologicalGroup K₀]
    {d : ℕ} (τ : K₀ →* Matrix (Fin d) (Fin d) ℂ) (hτ : Continuous τ)
    (i : Fin d) (x : Fin d → ℂ) : compactInverseCoordinateWeight τ hτ i x ∈ finiteWeights := by
  let f := compactInverseCoordinateWeight τ hτ i
  change FiniteVectors.IsFiniteVector leftRegular (f x)
  apply Submodule.finiteDimensional_of_le (S₂ := f.range)
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  refine ⟨τ k *ᵥ x, ?_⟩
  ext g
  exact compactInverseCoordinateWeight_translate τ hτ i k g x

/-- A surjective continuous smooth map respecting the orthogonal action lifts every
compact-finite target vector to a compact-finite source vector. -/
def RealSmoothCompactFiniteLiftingStatement : Prop :=
  ∀ (n : ℕ) (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (F : Type uF) [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (R : G n →* (E →L[ℂ] E)) (S : G n →* (F →L[ℂ] F))
    (Q : D n R →L[ℂ] D n S), IsContinuousRepresentation R → IsContinuousRepresentation S →
    Function.Surjective Q → (∀ (k : K n) v, Q (κ n R k v) = κ n S k (Q v)) →
    ∀ v ∈ smoothKFinite ℝ n S, ∃ w ∈ smoothKFinite ℝ n R, Q w = v

set_option maxHeartbeats 600000 in
theorem realSmoothCompactFiniteLifting : RealSmoothCompactFiniteLiftingStatement.{uE, uF} := by
  intro n E _ _ _ F _ _ _ R S Q hR hS hQs hQK v hv
  let W := FiniteVectors.orbitSubrepresentation (κ n S) v
  let : FiniteDimensional ℂ W.toSubmodule := hv
  let b := Module.finBasis ℂ W.toSubmodule
  let v₀ : W.toSubmodule := ⟨v, FiniteVectors.self_mem_orbitSpan (κ n S) v⟩
  let τ := Langlands.KFiniteDual.subMatrix W
  let hτ := continuous_subMatrix_smooth S hS W
  let w := fun i => compactInverseCoordinateWeight τ hτ i (b.equivFun v₀)
  let μ : Measure (K n) := Measure.haarMeasure ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩
  let : IsProbabilityMeasure μ := ⟨Measure.haarMeasure_self⟩
  choose x hx using fun i => hQs (b i : D n S)
  let y := ∑ i, orthogonalSmoothAverage R hR μ (x i) (w i)
  have hf (i : Fin (Module.finrank ℂ W.toSubmodule)) : w i ∈ finiteWeights :=
    compactInverseCoordinateWeight_mem_finiteWeights τ hτ i (b.equivFun v₀)
  refine ⟨y, (smoothKFinite ℝ n R).sum_mem (fun i _ =>
    orthogonalSmoothAverage_mem_smoothKFinite R hR μ (x i) (hf i)), ?_⟩
  have hrec (k : K n) : (∑ i, w i k • κ n S k (b i : D n S)) = v := by
    have hco : (∑ i, w i k • (b i : D n S)) = κ n S k⁻¹ v := by
      have he := Langlands.KFiniteDual.subMatrix_mulVec W k⁻¹ v₀
      have hc (i : Fin (Module.finrank ℂ W.toSubmodule)) : w i k =
          b.repr (W.toRepresentation k⁻¹ v₀) i := congrFun he i
      simp_rw [hc]
      change (∑ i, b.repr (W.toRepresentation k⁻¹ v₀) i • W.toSubmodule.subtype (b i)) =
        W.toSubmodule.subtype (W.toRepresentation k⁻¹ v₀)
      simpa only [map_sum, map_smul] using
        congrArg W.toSubmodule.subtype (b.sum_repr (W.toRepresentation k⁻¹ v₀))
    have he := congrArg (κ n S k) hco
    rw [map_sum] at he
    simp only [map_smul] at he
    rw [he, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  by_contra hne
  have hz : Q y - v ∉ (⊥ : Submodule ℂ (D n S)) := by
    simpa only [Submodule.mem_bot, sub_eq_zero] using hne
  obtain ⟨L, _, hL⟩ := exists_functional_vanishing_on_closedSubmodule
    (show IsClosed ((⊥ : Submodule ℂ (D n S)) : Set (D n S)) from isClosed_singleton) hz
  have hi (i : Fin (Module.finrank ℂ W.toSubmodule)) :
      L (Q (orthogonalSmoothAverage R hR μ (x i) (w i))) =
        ∫ k, w i k • L (κ n S k (b i : D n S)) ∂μ := by
    let j : C(K n, G n) := ⟨Unitary.toUnits, continuous_unitary_toUnits⟩
    have h := apply_compactSmoothAverage R hR μ j (w i) (x i) (L.comp Q)
    change L (Q (orthogonalSmoothAverage R hR μ (x i) (w i))) =
      ∫ k, w i k • L (Q (κ n R k (x i))) ∂μ at h
    simpa only [hQK, hx] using h
  apply hL
  rw [map_sub, sub_eq_zero]
  change L (Q (∑ i, orthogonalSmoothAverage R hR μ (x i) (w i))) = L v
  simp only [map_sum, hi]
  rw [← integral_finsetSum Finset.univ]
  · calc
      _ = ∫ _ : K n, L v ∂μ := by
        apply integral_congr_ae
        filter_upwards with k
        rw [← hrec k, map_sum]
        simp only [map_smul]
      _ = _ := by simp
  · intro i _
    have hcont : Continuous (fun k : K n => L (κ n S k (b i : D n S))) :=
      L.continuous.comp ((continuous_representation_units S hS).comp
        (continuous_unitary_toUnits.prodMk continuous_const))
    exact ((w i).continuous.smul hcont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

end Langlands.Archimedean
