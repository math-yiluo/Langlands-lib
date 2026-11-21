import Langlands.Representation.Archimedean.MixedSmoothExtension

/-! # Mixed functionals are determined by the dense original carrier -/

noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff

namespace Langlands.Archimedean.MixedSmooth

open Langlands.Archimedean.SmoothInvariantSubspace

universe uA uG uL uE uV

variable {A : Type uA} [NormedAddCommGroup A] [NormedSpace ℝ A]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace A G] [LieGroup 𝓘(ℝ, A) ∞ G]
  {L : Type uL} [Group L] [TopologicalSpace L]
  [LocallyCompactSpace L] [NonarchimedeanGroup L]
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ L V)
  (σ : L →* (E →L[ℂ] E)) (π : G →* (E →L[ℂ] E))
  (hcomm : ∀ g l x, π g (σ l x) = σ l (π g x))

local notation "I" => 𝓘(ℝ, A)
local notation "W" => Vectors (A := A) σ π hcomm

/-- Equality on the original vectors extends to the genuine mixed smooth
space when the source image is derivative-dense at each level. -/
theorem functional_eq_of_source_values
    (j : ρ.IntertwiningMap (finiteRepresentation (A := A) σ π hcomm))
    (s : V →ₗ[ℂ] Langlands.Archimedean.smoothVectors I π)
    (hj : ∀ v, (j v).val = s v) (hd : DenseFixedImages (A := A) ρ σ π s)
    (ℓ₀ ℓ₁ : W →ₗ[ℂ] ℂ)
    (h₀ : IsContinuousAtEachLevel (A := A) σ π hcomm ℓ₀)
    (h₁ : IsContinuousAtEachLevel (A := A) σ π hcomm ℓ₁)
    (he : ∀ v, ℓ₀ (j v) = ℓ₁ (j v)) :
    ℓ₀ = ℓ₁ := by
  apply LinearMap.ext
  intro w
  obtain ⟨J, hw⟩ := exists_compactLevel σ π hcomm w
  obtain ⟨f₀, hf₀, hval₀⟩ := h₀ J
  obtain ⟨f₁, hf₁, hval₁⟩ := h₁ J
  have hsource (v : Langlands.fixedVectors ρ J.toSubgroup) :
      f₀ (s v.val) = f₁ (s v.val) := by
    have hv : (j v.val).val.val ∈ fixedSubspace σ J.toSubgroup := by
      intro k
      have heq : finiteRepresentation (A := A) σ π hcomm (k : L) (j v.val) = j v.val :=
        (Representation.IntertwiningMap.isIntertwining ρ
          (finiteRepresentation (A := A) σ π hcomm) j (k : L) v.val).symm.trans
            (congrArg j (v.property k))
      exact congrArg (fun x : W => x.val.val) heq
    simpa only [hj] using
      (hval₀ (j v.val) hv).symm.trans ((he v.val).trans (hval₁ (j v.val) hv))
  exact (hval₀ w hw).trans
    ((continuousFunctional_eq_of_fixedImage ρ σ π s J (hd J) f₀ f₁ hf₀ hf₁ hsource w.val hw).trans
      (hval₁ w hw).symm)

/-- A nonzero derivative-continuous mixed functional is nonzero on the
original carrier. -/
theorem functional_source_ne_zero
    (j : ρ.IntertwiningMap (finiteRepresentation (A := A) σ π hcomm))
    (s : V →ₗ[ℂ] Langlands.Archimedean.smoothVectors I π)
    (hj : ∀ v, (j v).val = s v) (hd : DenseFixedImages (A := A) ρ σ π s)
    (ℓ : W →ₗ[ℂ] ℂ) (hℓ : IsContinuousAtEachLevel (A := A) σ π hcomm ℓ)
    (hne : ℓ ≠ 0) : ℓ.comp j.toLinearMap ≠ 0 := by
  intro hz
  apply hne
  exact functional_eq_of_source_values ρ σ π hcomm j s hj hd ℓ 0 hℓ
    (fun _ => ⟨0, ⟨∅, 0, by simp⟩, fun _ _ => rfl⟩)
    (fun v => LinearMap.congr_fun hz v)

/-- Proportionality on the original carrier gives proportionality of
the derivative-continuous mixed functionals. -/
theorem functional_eq_smul_of_source_values
    (j : ρ.IntertwiningMap (finiteRepresentation (A := A) σ π hcomm))
    (s : V →ₗ[ℂ] Langlands.Archimedean.smoothVectors I π)
    (hj : ∀ v, (j v).val = s v) (hd : DenseFixedImages (A := A) ρ σ π s)
    (ℓ₀ ℓ₁ : W →ₗ[ℂ] ℂ)
    (h₀ : IsContinuousAtEachLevel (A := A) σ π hcomm ℓ₀)
    (h₁ : IsContinuousAtEachLevel (A := A) σ π hcomm ℓ₁) (c : ℂ)
    (he : ℓ₁.comp j.toLinearMap = c • ℓ₀.comp j.toLinearMap) :
    ℓ₁ = c • ℓ₀ := by
  apply functional_eq_of_source_values ρ σ π hcomm j s hj hd ℓ₁ (c • ℓ₀) h₁
  · intro J
    obtain ⟨f, hf, hval⟩ := h₀ J
    refine ⟨c • f, ?_, fun x hx => congrArg (c • ·) (hval x hx)⟩
    exact (continuous_iff_isContinuousOnSmoothVectors I π (c • f)).mp
      ((continuous_of_isContinuousOnSmoothVectors I π f hf).const_smul c)
  · exact fun v => LinearMap.congr_fun he v

end Langlands.Archimedean.MixedSmooth
