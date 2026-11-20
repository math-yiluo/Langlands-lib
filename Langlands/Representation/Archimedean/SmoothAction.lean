import Langlands.Representation.Archimedean.SmoothDerivativeTopology
import Mathlib.Topology.DenseEmbedding

/-! # Group action on the genuine derivative topology -/

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace Langlands.Archimedean.SmoothAction

universe u𝔤 uH uG uE uV

variable {𝔤 : Type u𝔤} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤]
  {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ 𝔤 H)
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (π : G →* (E →L[ℂ] E)) [LieGroup I ∞ G]

/-- The real tangent map of conjugation by the inverse of a fixed group element. -/
def conjugateDirection (g : G) : 𝔤 →L[ℝ] 𝔤 :=
  mfderiv I I (fun h : G => g⁻¹ * h * g) 1

set_option backward.isDefEq.respectTransparency false in
/-- The genuine derived action of a translated vector is the translated action
in the conjugated tangent direction. -/
theorem lieDerivative_apply (g : G) (X : 𝔤) {v : E}
    (hv : IsSmoothVector I π v) :
    lieDerivative I π X (π g v) =
      π g (lieDerivative I π (conjugateDirection I g X) v) := by
  let c : G → G := fun h => g⁻¹ * h * g
  let A := (π g).restrictScalars ℝ
  have hc : ContMDiff I I ∞ c :=
    (contMDiff_const.mul contMDiff_id).mul contMDiff_const
  have hc₀ : MDifferentiableAt I I c 1 := hc.mdifferentiableAt (by simp)
  have hc₁ : c 1 = 1 := by simp [c]
  have hf : MDifferentiableAt I 𝓘(ℝ, E) (orbitMap π v) (c 1) := by
    rw [hc₁]
    exact hv.mdifferentiableAt (by simp)
  have hfc := hf.comp 1 hc₀
  have hA : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) A ((orbitMap π v ∘ c) 1) :=
    A.differentiableAt.mdifferentiableAt
  have he : orbitMap π (π g v) = A ∘ (orbitMap π v ∘ c) := by
    funext h
    change π h (π g v) = π g (π (g⁻¹ * h * g) v)
    calc
      π h (π g v) = π (h * g) v := by rw [map_mul, mul_apply_eq_comp]
      _ = π (g * (g⁻¹ * h * g)) v := by simp only [← mul_assoc, mul_inv_cancel, one_mul]
      _ = π g (π (g⁻¹ * h * g) v) := by rw [map_mul, mul_apply_eq_comp]
  unfold Langlands.Archimedean.lieDerivative
  rw [he, mfderiv_comp 1 hA hfc, ContinuousLinearMap.mfderiv_eq,
    mfderiv_comp 1 hf hc₀, hc₁]
  rfl

/-- Every genuine word transforms by the same inverse-conjugation tangent map. -/
theorem iteratedLieDerivative_apply (g : G) (Xs : List 𝔤) {v : E}
    (hv : IsSmoothVector I π v) :
    iteratedLieDerivative I π Xs (π g v) =
      π g (iteratedLieDerivative I π (Xs.map (conjugateDirection I g)) v) := by
  induction Xs with
  | nil => rfl
  | cons X Xs ih =>
      simp only [iteratedLieDerivative_cons, List.map_cons, ih]
      apply lieDerivative_apply I π g X
      have hs : IsSmoothVector I π
          (smoothIteratedLieDerivative I π (Xs.map (conjugateDirection I g)) ⟨v, hv⟩ : E) :=
        (smoothIteratedLieDerivative I π (Xs.map (conjugateDirection I g)) ⟨v, hv⟩).property
      simpa only [smoothIteratedLieDerivative_apply] using hs

/-- The genuine word seminorm of a translated vector is bounded by one
conjugated word seminorm and the original operator norm. -/
theorem wordSeminorm_apply_le (g : G) (Xs : List 𝔤) (v : smoothVectors I π) :
    wordSeminorm I π Xs (smoothRepresentation I π g v) ≤
      ‖π g‖ * wordSeminorm I π (Xs.map (conjugateDirection I g)) v := by
  rw [wordSeminorm_apply, wordSeminorm_apply, smoothRepresentation_apply,
    iteratedLieDerivative_apply I π g Xs v.property]
  exact (π g).le_opNorm _

/-- The action of a fixed group element on the derivative-topology copy. -/
def derivativeActionLinear (g : G) :
    DerivativeSmoothVectors I π →ₗ[ℂ] DerivativeSmoothVectors I π :=
  (DerivativeSmoothVectors.toSmooth I π).symm.toLinearMap.comp
    ((smoothRepresentation I π g).comp (DerivativeSmoothVectors.toSmooth I π).toLinearMap)

@[simp]
theorem toSmooth_derivativeActionLinear (g : G) (v : DerivativeSmoothVectors I π) :
    DerivativeSmoothVectors.toSmooth I π (derivativeActionLinear I π g v) =
      smoothRepresentation I π g (DerivativeSmoothVectors.toSmooth I π v) := rfl

theorem derivativeCoordinates_derivativeActionLinear (g : G)
    (v : DerivativeSmoothVectors I π) (Xs : List 𝔤) :
    DerivativeSmoothVectors.derivativeCoordinates I π (derivativeActionLinear I π g v) Xs =
      π g (DerivativeSmoothVectors.derivativeCoordinates I π v
        (Xs.map (conjugateDirection I g))) := by
  simp only [DerivativeSmoothVectors.derivativeCoordinates_apply,
    toSmooth_derivativeActionLinear, smoothRepresentation_apply]
  exact iteratedLieDerivative_apply I π g Xs (DerivativeSmoothVectors.toSmooth I π v).property

/-- Each fixed group element acts continuously for the genuine derivative topology. -/
theorem continuous_derivativeActionLinear (g : G) :
    Continuous (derivativeActionLinear I π g) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro Xs
  change Continuous (fun v => DerivativeSmoothVectors.derivativeCoordinates I π
    (derivativeActionLinear I π g v) Xs)
  simp_rw [derivativeCoordinates_derivativeActionLinear]
  exact (π g).continuous.comp
    (DerivativeSmoothVectors.derivativeCLM I π (Xs.map (conjugateDirection I g))).continuous

/-- The continuous linear action of a fixed group element on genuine derivative vectors. -/
def derivativeAction (g : G) :
    DerivativeSmoothVectors I π →L[ℂ] DerivativeSmoothVectors I π :=
  ⟨derivativeActionLinear I π g, continuous_derivativeActionLinear I π g⟩

@[simp]
theorem toSmooth_derivativeAction (g : G) (v : DerivativeSmoothVectors I π) :
    DerivativeSmoothVectors.toSmooth I π (derivativeAction I π g v) =
      smoothRepresentation I π g (DerivativeSmoothVectors.toSmooth I π v) := rfl

/-- Every derivative coordinate of the continuous fixed-element action. -/
theorem derivativeCoordinates_derivativeAction (g : G)
    (v : DerivativeSmoothVectors I π) (Xs : List 𝔤) :
    DerivativeSmoothVectors.derivativeCoordinates I π (derivativeAction I π g v) Xs =
      π g (DerivativeSmoothVectors.derivativeCoordinates I π v
        (Xs.map (conjugateDirection I g))) :=
  derivativeCoordinates_derivativeActionLinear I π g v Xs

/-- The group representation on the copy with genuine derivative topology.
This asserts continuity for each fixed element, not joint continuity. -/
def derivativeRepresentation :
    G →* (DerivativeSmoothVectors I π →L[ℂ] DerivativeSmoothVectors I π) where
  toFun := derivativeAction I π
  map_one' := by
    apply ContinuousLinearMap.ext
    intro v
    apply (DerivativeSmoothVectors.toSmooth I π).injective
    simp only [toSmooth_derivativeAction, map_one, Module.End.one_apply,
      one_apply_eq_self]
  map_mul' g h := by
    apply ContinuousLinearMap.ext
    intro v
    apply (DerivativeSmoothVectors.toSmooth I π).injective
    simp only [toSmooth_derivativeAction, map_mul, Module.End.mul_apply,
      mul_apply_eq_comp, toSmooth_derivativeAction]

@[simp]
theorem derivativeRepresentation_apply (g : G) :
    derivativeRepresentation I π g = derivativeAction I π g :=
  rfl

/-- After forgetting the derivative topology, the packaged representation is the
published smooth action. -/
theorem toSmooth_derivativeRepresentation (g : G) (v : DerivativeSmoothVectors I π) :
    DerivativeSmoothVectors.toSmooth I π (derivativeRepresentation I π g v) =
      smoothRepresentation I π g (DerivativeSmoothVectors.toSmooth I π v) :=
  rfl

/-- Pullback along a fixed smooth group element preserves genuine finite-word continuity. -/
theorem isContinuousOnSmoothVectors_comp (g : G)
    (L : smoothVectors I π →ₗ[ℂ] ℂ) (hL : IsContinuousOnSmoothVectors I π L) :
    IsContinuousOnSmoothVectors I π (L.comp (smoothRepresentation I π g)) := by
  apply isContinuousOnSmoothVectors_of_continuous
  exact (continuous_of_isContinuousOnSmoothVectors I π L hL).comp
    (derivativeAction I π g).continuous

section DenseExtensions

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (j : V →ₗ[ℂ] smoothVectors I π)

/-- The same algebraic embedding, valued in the dedicated derivative-topology copy. -/
def derivativeEmbedding : V →ₗ[ℂ] DerivativeSmoothVectors I π :=
  (DerivativeSmoothVectors.toSmooth I π).symm.toLinearMap.comp j

omit [LieGroup I ∞ G] in
@[simp]
theorem toSmooth_derivativeEmbedding (v : V) :
    DerivativeSmoothVectors.toSmooth I π (derivativeEmbedding I π j v) = j v :=
  (DerivativeSmoothVectors.toSmooth I π).apply_symm_apply (j v)

/-- Genuine derivative-topology density makes continuous scalar extensions unique. -/
theorem eq_of_agree_on_dense_embedding
    (hd : DenseRange (derivativeEmbedding I π j))
    (L₀ L₁ : smoothVectors I π →ₗ[ℂ] ℂ)
    (hL₀ : IsContinuousOnSmoothVectors I π L₀)
    (hL₁ : IsContinuousOnSmoothVectors I π L₁)
    (hagree : ∀ v, L₀ (j v) = L₁ (j v)) : L₀ = L₁ := by
  have h := hd.equalizer
    (continuous_of_isContinuousOnSmoothVectors I π L₀ hL₀)
    (continuous_of_isContinuousOnSmoothVectors I π L₁ hL₁)
    (by funext v; simpa only [Function.comp_apply, toSmooth_derivativeEmbedding] using hagree v)
  ext v
  simpa only [LinearEquiv.apply_symm_apply] using
    congrFun h ((DerivativeSmoothVectors.toSmooth I π).symm v)

/-- Covariance on a supplied derivative-dense image extends to all genuine
smooth vectors. The density hypothesis is stronger than Hilbert norm density. -/
theorem isWhittakerFunctional_of_dense_embedding
    (hd : DenseRange (derivativeEmbedding I π j))
    (N : Subgroup G) (χ : N →* ℂˣ)
    (L : smoothVectors I π →ₗ[ℂ] ℂ) (hL : IsContinuousOnSmoothVectors I π L)
    (hcov : ∀ (u : N) (v : V),
      L (smoothRepresentation I π (u : G) (j v)) = (χ u : ℂ) * L (j v)) :
    IsWhittakerFunctional I π N χ L := by
  refine ⟨hL, ?_⟩
  intro u v
  have hc := continuous_of_isContinuousOnSmoothVectors I π L hL
  have h := hd.equalizer
    (hc.comp (derivativeAction I π (u : G)).continuous)
    (continuous_const.mul hc)
    (by funext w; simpa only [Function.comp_apply, Pi.mul_apply, toSmooth_derivativeAction,
      toSmooth_derivativeEmbedding] using hcov u w)
  simpa only [Function.comp_apply, Pi.mul_apply, LinearEquiv.apply_symm_apply,
    toSmooth_derivativeAction] using
    congrFun h ((DerivativeSmoothVectors.toSmooth I π).symm v)

end DenseExtensions

end Langlands.Archimedean.SmoothAction
