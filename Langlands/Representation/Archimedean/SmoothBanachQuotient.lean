import Langlands.Representation.Archimedean.SmoothVectorSubgroupFactorization
import Langlands.Geometry.Manifold.LinearLieGroup.Units

/-! # Surjectivity on smooth vectors of Banach quotients -/

noncomputable section

open MeasureTheory Set
open scoped Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open DerivativeSmoothVectors Langlands.LinearLieGroup

universe uA uE uF

section Factorization

variable {A : Type uA} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [FiniteDimensional ℝ A] [MeasurableSpace Aˣ] [BorelSpace Aˣ]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (R : Aˣ →* (E →L[ℂ] E)) (μ : Measure Aˣ) [μ.IsHaarMeasure]

local notation "I" => 𝓘(ℝ, A)
local notation "D" => DerivativeSmoothVectors I R
local notation "ε" => derivativeCLM I R []

private def unitsTopEquiv (A : Type uA) [NormedRing A] :
    Aˣ ≃ₜ* (⊤ : Subgroup Aˣ) :=
  { (Subgroup.topEquiv (G := Aˣ)).symm with
    continuous_toFun := continuous_id.subtype_mk _
    continuous_invFun := continuous_subtype_val }

/-- A genuine smooth vector for the units group is a finite sum of averaged vectors,
with smooth compact kernels on the units group itself. -/
theorem exists_sum_smoothAverage_units (hR : IsContinuousRepresentation R) (v : D) :
    ∃ (m : ℕ) (w : Fin m → D) (κ : Fin m → Aˣ → ℂ),
      (∀ i, ContMDiff I 𝓘(ℝ, ℂ) ∞ (κ i) ∧ HasCompactSupport (κ i)) ∧
      ε v = ∑ i, smoothedVector R μ (κ i) (ε (w i)) := by
  let K := (⊤ : Subgroup Aˣ)
  let e : Aˣ ≃ₜ* K := unitsTopEquiv A
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  let ν := μ.map e
  let : ν.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ e
  obtain ⟨m, w, f, hf, heval⟩ := smoothVectorSubgroupFactorization A E R K
    (⊤ : Submodule ℝ A) (isExpLieAlgebra_top (𝔸 := A)) ν hR univ Filter.univ_mem v
  let κ (i : Fin m) (g : Aˣ) := f i (e g⁻¹)
  have hc (i : Fin m) : ContMDiff I 𝓘(ℝ, ℂ) ∞ (fun g => f i (e g)) := by
    apply (contMDiff_units_iff_top (fun g => f i (e g))).2
    exact (hf i).1
  have hs (i : Fin m) : ContMDiff I 𝓘(ℝ, ℂ) ∞ (κ i) := (hc i).comp (contMDiff_inv I ∞)
  have hk (i : Fin m) : HasCompactSupport (κ i) :=
    (hf i).2.1.comp_homeomorph ((Homeomorph.inv Aˣ).trans e.toHomeomorph)
  refine ⟨m, w, κ, fun i => ⟨hs i, hk i⟩, ?_⟩
  by_contra hne
  let u := ε v - ∑ i, smoothedVector R μ (κ i) (ε (w i))
  have hu : u ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨L, -, hL⟩ := exists_dual_vector ℂ u (norm_ne_zero_iff.mpr hu)
  let T := L.comp ε
  have hT := heval T
  have hterm (i : Fin m) : (∫ x : K, f i x * T (representation I R (x : Aˣ) (w i)) ∂ν) =
      L (smoothedVector R μ (κ i) (ε (w i))) := by
    have hmap := integral_map_equiv (μ := μ) e.toHomeomorph.toMeasurableEquiv
      (fun x : K => f i x * T (representation I R (x : Aˣ) (w i)))
    change (∫ x : K, f i x * T (representation I R (x : Aˣ) (w i)) ∂ν) =
      ∫ x : Aˣ, f i (e x) * T (representation I R x (w i)) ∂μ at hmap
    rw [hmap]
    have hv : Continuous (fun x : Aˣ => R x (ε (w i))) :=
      hR.comp (continuous_id.prodMk continuous_const)
    have hi : Integrable (fun x : Aˣ => κ i x⁻¹ • R x (ε (w i))) μ :=
      (((hs i).continuous.comp continuous_inv).smul hv).integrable_of_hasCompactSupport
        (((hk i).comp_homeomorph (Homeomorph.inv Aˣ)).smul_right)
    rw [smoothedVector, ← L.integral_comp_comm hi]
    apply integral_congr_ae
    filter_upwards with x
    rw [map_smul, smul_eq_mul]
    change f i (e x) * (L (R x (ε (w i)))) = κ i x⁻¹ * L (R x (ε (w i)))
    rw [show κ i x⁻¹ = f i (e x) by simp [κ]]
  simp_rw [hterm] at hT
  have hz : L u = 0 := by
    dsimp only [u]
    rw [map_sub, map_sum, ← hT]
    exact sub_self (T v)
  rw [hz] at hL
  exact hu (norm_eq_zero.mp (by simpa using (congrArg (fun z : ℂ => ‖z‖) hL).symm))

end Factorization

/-- A surjective bounded equivariant map of jointly continuous Banach representations of
an actual units group is surjective on the smooth vectors. -/
def SmoothBanachQuotientStatement : Prop :=
  ∀ {A : Type uA} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    [FiniteDimensional ℝ A] {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (R : Aˣ →* (E →L[ℂ] E)) (S : Aˣ →* (F →L[ℂ] F))
    (T : E →L[ℂ] F), IsContinuousRepresentation R → IsContinuousRepresentation S →
    Function.Surjective T → (∀ g x, T (R g x) = S g (T x)) →
    ∀ v : F, IsSmoothVector 𝓘(ℝ, A) S v →
      ∃ u : E, IsSmoothVector 𝓘(ℝ, A) R u ∧ T u = v

theorem smoothBanachQuotient : SmoothBanachQuotientStatement.{uA, uE, uF} := by
  intro A _ _ _ _ E _ _ _ F _ _ _ R S T hR hS hT hGS v hv
  let : LocallyCompactSpace Aˣ := Units.isOpenEmbedding_val.locallyCompactSpace
  let : MeasurableSpace Aˣ := borel Aˣ
  let : BorelSpace Aˣ := ⟨rfl⟩
  let μ := (Measure.haar : Measure Aˣ)
  let vSmooth := (toSmooth 𝓘(ℝ, A) S).symm ⟨v, hv⟩
  obtain ⟨m, w, κ, hκ, heq⟩ := exists_sum_smoothAverage_units S μ hS vSmooth
  choose u hu using fun i : Fin m => hT (derivativeCLM 𝓘(ℝ, A) S [] (w i))
  let y (i : Fin m) := smoothedVector R μ (κ i) (u i)
  refine ⟨∑ i, y i, (smoothVectors 𝓘(ℝ, A) R).sum_mem (fun i _ =>
    isSmoothVector_smoothedVector R μ hR (hκ i).1 (hκ i).2 (u i)), ?_⟩
  rw [map_sum]
  have hv' : derivativeCLM 𝓘(ℝ, A) S [] vSmooth = v := by
    change ((toSmooth 𝓘(ℝ, A) S) vSmooth : F) = v
    rw [LinearEquiv.apply_symm_apply]
  rw [hv'] at heq
  rw [heq]
  refine Finset.sum_congr rfl fun i _ => ?_
  have horb : Continuous (fun g : Aˣ => R g (u i)) :=
    hR.comp (continuous_id.prodMk continuous_const)
  have hi : Integrable (fun g : Aˣ => κ i g⁻¹ • R g (u i)) μ :=
    (((hκ i).1.continuous.comp continuous_inv).smul horb).integrable_of_hasCompactSupport
      ((((hκ i).2).comp_homeomorph (Homeomorph.inv Aˣ)).smul_right)
  change T (smoothedVector R μ (κ i) (u i)) =
    smoothedVector S μ (κ i) (derivativeCLM 𝓘(ℝ, A) S [] (w i))
  rw [smoothedVector, smoothedVector, ← T.integral_comp_comm hi]
  apply integral_congr_ae
  filter_upwards with g
  rw [map_smul, hGS, hu]

end Langlands.Archimedean
