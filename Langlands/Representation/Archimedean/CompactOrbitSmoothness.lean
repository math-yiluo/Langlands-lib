import Langlands.Representation.Archimedean.CompactWeightedOrbit
import Langlands.Representation.Archimedean.BanachOrbitSmoothing
import Langlands.Analysis.CompactParameterSmoothness

/-! # Smoothness of compactly averaged orbit vectors -/

noncomputable section

open MeasureTheory Set Topology
open scoped ContDiff Manifold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Bochner integration on the space of continuous functions on a compact
finite-measure space. -/
def compactBochnerIntegral : C(X, E) →L[ℝ] E := by
  have hInt (f : C(X, E)) : Integrable f ν :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let T : C(X, E) →ₗ[ℝ] E :=
    { toFun := fun f => ∫ x, f x ∂ν
      map_add' := fun f g => integral_add (hInt f) (hInt g)
      map_smul' := fun c f => integral_smul c f }
  refine T.mkContinuous (ν.real univ) (fun f => ?_)
  change ‖∫ x, f x ∂ν‖ ≤ ν.real univ * ‖f‖
  rw [mul_comm]
  exact norm_integral_le_of_norm_le_const
    (Filter.Eventually.of_forall (f.norm_coe_le_norm))

omit [CompleteSpace E] in
@[simp]
theorem compactBochnerIntegral_apply (f : C(X, E)) :
    compactBochnerIntegral ν f = ∫ x, f x ∂ν := rfl

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  (R : Aˣ →* (E →L[ℂ] E)) (hR : IsContinuousRepresentation R)
  (j : C(X, Aˣ)) (w : C(X, ℂ))

local notation "I" => 𝓘(ℝ, A)
local notation "U" => Set.range (Units.val : Aˣ → A)

/-- Compact weighted averaging preserves smooth vectors. The continuous group parameter and
weight are held fixed while differentiating the orbit variable. -/
theorem isSmoothVector_compactWeightedOrbit {v : E} (hv : IsSmoothVector I R v) :
    IsSmoothVector I R (compactWeightedOrbit ν R hR j w v) := by
  classical
  let c : OpenPartialHomeomorph Aˣ A :=
    Units.isOpenEmbedding_val.toOpenPartialHomeomorph (Units.val : Aˣ → A)
  have hc : ContMDiffOn I I ∞ c.symm U :=
    contMDiffOn_isOpenEmbedding_symm («I» := I) Units.isOpenEmbedding_val
  have hval (g : Aˣ) : c.symm (g : A) = g :=
    Units.isOpenEmbedding_val.toOpenPartialHomeomorph_left_inv (Units.val : Aˣ → A)
  let H : A × A → E := fun p => R (c.symm p.1 * c.symm p.2) v
  have hG : ContMDiff ((I).prod I) 𝓘(ℝ, E) ∞ (fun p : Aˣ × Aˣ => R (p.1 * p.2) v) :=
    hv.comp (contMDiff_fst.mul contMDiff_snd)
  have hH : ContDiffOn ℝ ∞ H (U ×ˢ U) := by
    have h := (hG.contMDiffOn (s := (univ : Set (Aˣ × Aˣ)))).comp (hc.prodMap hc)
      (fun _ _ => mem_univ _)
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
    exact h.contDiffOn
  let F : A × (A × ℂ) → E := fun p => p.2.2 • H (p.1, p.2.1)
  have hF : ContDiffOn ℝ ∞ F (U ×ˢ (U ×ˢ univ)) := by
    have hp : ContDiff ℝ ∞ (fun p : A × (A × ℂ) => (p.1, p.2.1)) :=
      contDiff_fst.prodMk contDiff_snd.fst
    exact contDiff_snd.snd.contDiffOn.smul
      (hH.comp hp.contDiffOn (fun _ hx => ⟨hx.1, hx.2.1⟩))
  let a : C(X, A × ℂ) :=
    ⟨fun x => ((j x).val, w x), (Units.continuous_val.comp j.continuous).prodMk w.continuous⟩
  have ha (x : X) : a x ∈ (U ×ˢ univ) := ⟨⟨j x, rfl⟩, mem_univ _⟩
  let f (g : A) : C(X, E) :=
    if hg : g ∈ U then
      ⟨fun x => F (g, a x), hF.continuousOn.comp_continuous
        (continuous_const.prodMk a.continuous) (fun x => ⟨hg, ha x⟩)⟩
    else 0
  have he (g : A) (hg : g ∈ U) (x : X) : f g x = F (g, a x) := by
    simp only [f, dite_eq_left hg, ContinuousMap.coe_mk]
  have hs : IsOpen U := Units.isOpenEmbedding_val.isOpen_range
  have hf := Langlands.Analysis.contDiffOn_infty_compactFamily_of_joint a hs
    (hs.prod isOpen_univ) ha hF he
  let L := compactBochnerIntegral (E := E) ν
  have hL : ContDiffOn ℝ ∞ (fun g => L (f g)) U := L.contDiff.comp_contDiffOn hf
  have h := hL.contMDiffOn.comp_contMDiff (Units.contMDiff_val (n := ∞)) (fun g => ⟨g, rfl⟩)
  change ContMDiff I 𝓘(ℝ, E) ∞ (fun g => R g (compactWeightedOrbit ν R hR j w v))
  refine h.congr fun g => ?_
  change R g (compactWeightedOrbit ν R hR j w v) = L (f (g : A))
  rw [compactWeightedOrbit_apply, compactBochnerIntegral_apply,
    ← (R g).integral_comp_comm (integrable_compactWeightedOrbit ν R hR j w v)]
  apply integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  rw [he _ ⟨g, rfl⟩ x]
  change R g (w x • R (j x) v) = w x • R (c.symm (g : A) * c.symm (j x : A)) v
  rw [map_smul, hval, hval, map_mul, mul_apply_eq_comp]

variable [FiniteDimensional ℝ A] [MeasurableSpace Aˣ] [BorelSpace Aˣ]
  (μ : Measure Aˣ) [μ.IsHaarMeasure]

include μ in
/-- If the compact orbit average has finite-dimensional range, every vector in its range
is genuinely smooth, by density of smooth input vectors and closedness in that range. -/
theorem isSmoothVector_compactWeightedOrbit_of_finiteRange
    (hfin : FiniteDimensional ℂ (compactWeightedOrbit ν R hR j w).toLinearMap.range) (v : E) :
    IsSmoothVector I R (compactWeightedOrbit ν R hR j w v) := by
  let T := compactWeightedOrbit ν R hR j w
  let M := T.toLinearMap.range
  let F : E →L[ℂ] M := T.codRestrict M (fun u => ⟨u, rfl⟩)
  let S := (smoothVectors I R).comap M.subtype
  let : FiniteDimensional ℂ M := hfin
  have hclosed : IsClosed (F ⁻¹' (S : Set M)) :=
    S.closed_of_finiteDimensional.preimage F.continuous
  have hle : (smoothVectors I R : Set E) ⊆ F ⁻¹' (S : Set M) := by
    intro u hu
    exact isSmoothVector_compactWeightedOrbit ν R hR j w hu
  exact closure_minimal hle hclosed (dense_smoothVectors_units R μ hR v)

end Langlands.Archimedean
