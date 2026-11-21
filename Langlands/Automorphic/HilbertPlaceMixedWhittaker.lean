import Langlands.Automorphic.HilbertPlaceFixedLevel
import Langlands.Representation.Archimedean.MixedFixedSmoothMap
import Langlands.Representation.Archimedean.UnitaryCompactAdmissibility

/-! # Comparing mixed Whittaker restrictions on a single Hilbert place component -/

noncomputable section
open scoped Manifold ContDiff Matrix.Norms.Operator TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000

namespace Langlands.Automorphic

open Langlands.Archimedean DerivativeSmoothVectors SmoothInvariantSubspace MixedSmooth
universe uA uG uL uV uE
attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type uA} [NormedAddCommGroup A] [NormedSpace ℝ A]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace A G] [LieGroup 𝓘(ℝ, A) ∞ G]
  {L : Type uL} [Group L] [TopologicalSpace L]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (σ : L →* (E →L[ℂ] E)) (π : G →* (E →L[ℂ] E))
  (hcomm : ∀ g l x, π g (σ l x) = σ l (π g x))
  (U : OpenSubgroup L) (j : V →ₗ[ℂ] E) (W : Submodule ℂ V)

local notation "I" => 𝓘(ℝ, A)
local notation "X" => Vectors (A := A) σ π hcomm
local notation "Efix" => fixedSubspace σ U.toSubgroup

variable {𝕜 : Type} [RCLike 𝕜] (r : ℕ)

local notation "M" => Matrix (Fin (r + 1)) (Fin (r + 1)) 𝕜
local notation "K" => Matrix.unitaryGroup (Fin (r + 1)) 𝕜

/-- Mixed evaluations with the same local Whittaker character are proportional
on a fixed algebraic component when the first restriction is nonzero. -/
theorem proportional_mixedRestrictions_of_placeFixedSmoothRealization
    (hUnique : UnitaryWhittakerMultiplicityOneOver.{uE} 𝕜)
    (i : Langlands.GeneralLinear (r + 1) 𝕜 →* G)
    (κ : Representation ℂ K V) (d : (ℂ ⊗[ℝ] M) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (hR : HasPlaceFixedSmoothRealization (𝔞 := A) π σ i j Unitary.toUnits κ d
      hcomm U.toSubgroup W)
    (j₀ : V →ₗ[ℂ] X) (hj₀ : ∀ v, (j₀ v).val.val = j v)
    (ψ : Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter 𝕜)
    (ℓ₀ ℓ₁ : X →ₗ[ℂ] ℂ) (f₀ f₁ : Langlands.Archimedean.smoothVectors I π →ₗ[ℂ] ℂ)
    (h₀ : IsContinuousOnSmoothVectors I π f₀) (h₁ : IsContinuousOnSmoothVectors I π f₁)
    (he₀ : ∀ w : X, w.val.val ∈ Efix → ℓ₀ w = f₀ w.val)
    (he₁ : ∀ w : X, w.val.val ∈ Efix → ℓ₁ w = f₁ w.val)
    (hc₀ : ∀ u : Langlands.GeneralLinear.upperUnipotent (r + 1) 𝕜, ∀ w : X,
      ℓ₀ (archimedeanRepresentation σ π hcomm (i u.val) w) =
        (Langlands.Whittaker.standardCharacter ψ r u : ℂ) * ℓ₀ w)
    (hc₁ : ∀ u : Langlands.GeneralLinear.upperUnipotent (r + 1) 𝕜, ∀ w : X,
      ℓ₁ (archimedeanRepresentation σ π hcomm (i u.val) w) =
        (Langlands.Whittaker.standardCharacter ψ r u : ℂ) * ℓ₁ w)
    (hn : ℓ₀.comp (j₀.comp W.subtype) ≠ 0) :
    ∃ c : ℂ, ℓ₁.comp (j₀.comp W.subtype) = c • ℓ₀.comp (j₀.comp W.subtype) := by
  obtain ⟨hplace, hW, hGK, P, hP⟩ := hR
  let R := placeClosureRepresentation (π.comp i) j Unitary.toUnits κ d hplace W hW
  let C := (LinearMap.range (j.comp W.subtype)).topologicalClosure
  let : CompleteSpace C := (LinearMap.range (j.comp W.subtype)).isClosed_topologicalClosure.completeSpace_coe
  let J := matrixModel 𝕜 (r + 1)
  have hGK' : IsGKHilbertRealization (Unitary.toUnits : K →* Mˣ)
      (PlaceComponent.restrictCompact hW) (PlaceComponent.restrictLie hW)
      R (rangeClosureEmbedding (j.comp W.subtype)) := hGK
  obtain ⟨hcont, hirr, hinner, hadm, _, _, _, _, hs, _⟩ := hGK'
  let js : W →ₗ[ℂ] Langlands.Archimedean.smoothVectors J R :=
    (rangeClosureEmbedding (j.comp W.subtype)).codRestrict _ hs
  let m := ofFixedDerivativeMap σ π hcomm U R P
  let L₀ := ℓ₀.comp m
  let L₁ := ℓ₁.comp m
  have hmap (v : W) : m (js v) = j₀ v := by
    apply Subtype.ext
    apply Subtype.ext
    rw [ofFixedDerivativeMap_val, hP, LinearEquiv.apply_symm_apply, hj₀]
    rfl
  have heq (ℓ : X →ₗ[ℂ] ℂ) : (ℓ.comp m).comp js = ℓ.comp (j₀.comp W.subtype) :=
    LinearMap.ext fun v => congrArg ℓ (hmap v)
  let T := C.subtypeL
  have hT (g : Langlands.GeneralLinear (r + 1) 𝕜) (v : C) : T (R g v) = π (i g) (T v) := rfl
  have hw₀ := isWhittakerFunctional_comp_ofFixedDerivativeMap σ π hcomm U R P i T hT hP
    (Langlands.GeneralLinear.upperUnipotent (r + 1) 𝕜) (Langlands.Whittaker.standardCharacter ψ r)
    ℓ₀ f₀ h₀ he₀ hc₀
  have hw₁ := isWhittakerFunctional_comp_ofFixedDerivativeMap σ π hcomm U R P i T hT hP
    (Langlands.GeneralLinear.upperUnipotent (r + 1) 𝕜) (Langlands.Whittaker.standardCharacter ψ r)
    ℓ₁ f₁ h₁ he₁ hc₁
  have hn' : L₀.comp js ≠ 0 := (heq ℓ₀).symm ▸ hn
  obtain ⟨c, h⟩ := proportional_whittakerRestrictions_of_unitaryUniqueness hUnique r R
    hcont hinner hirr hadm ψ L₀ L₁ hw₀ hw₁ js hn'
  exact ⟨c, (heq ℓ₁).symm.trans (h.trans (congrArg (c • ·) (heq ℓ₀)))⟩

end Langlands.Automorphic
