import Langlands.Automorphic.HilbertPlaceRealization
import Langlands.Representation.Archimedean.HilbertPlaceSmooth

/-! # Realizing a place component in a fixed Hilbert level -/

noncomputable section
open scoped ContDiff Manifold TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000

namespace Langlands.Automorphic

open Langlands.Archimedean DerivativeSmoothVectors SmoothInvariantSubspace
open HilbertCoefficientComparison
universe ua ub uG uA uK uL uV uH
attribute [local instance 100] LieRing.ofAssociativeRing

variable {𝔤 : Type ua} [NormedRing 𝔤] [NormedAlgebra ℝ 𝔤]
  {𝔞 : Type ub} [NormedAddCommGroup 𝔞] [NormedSpace ℝ 𝔞]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace 𝔤 G] [LieGroup 𝓘(ℝ, 𝔤) ∞ G]
  {A : Type uA} [Group A] [TopologicalSpace A] [ChartedSpace 𝔞 A] [LieGroup 𝓘(ℝ, 𝔞) ∞ A]
  {K : Type uK} [Group K] [TopologicalSpace K] {L : Type uL} [Group L]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (σ : A →* (H →L[ℂ] H)) (τ : L →* (H →L[ℂ] H))
  (i : G →* A) (j : V →ₗ[ℂ] H) (iK : K →* G)
  (κ : Representation ℂ K V) (d : (ℂ ⊗[ℝ] 𝔤) →ₗ⁅ℂ⁆ Module.End ℂ V)
  (hcomm : ∀ g l v, σ g (τ l v) = τ l (σ g v)) (U : Subgroup L) (W : Submodule ℂ V)

local notation "I" => 𝓘(ℝ, 𝔤)
local notation "J" => 𝓘(ℝ, 𝔞)

/-- The actual place closure realizes the original compact and Lie module and
its smooth vectors map continuously to the supplied fixed level by inclusion. -/
def HasPlaceFixedSmoothRealization : Prop :=
  ∃ (hplace : PlaceClosureCompatibility (σ.comp i) j iK κ d)
    (hW : PlaceComponent.IsStable κ d W),
    IsPlaceHilbertRealization (σ.comp i) j iK κ d hplace W hW ∧
    let R := placeClosureRepresentation (σ.comp i) j iK κ d hplace W hW
    ∃ M : DerivativeSmoothVectors I R →L[ℂ]
        DerivativeSmoothVectors J (fixedRestriction τ U σ hcomm),
      ∀ v, ((toSmooth J (fixedRestriction τ U σ hcomm) (M v) : fixedSubspace τ U) : H) =
        (toSmooth I R v : (LinearMap.range (j.comp W.subtype)).topologicalClosure).val

variable [CompleteSpace H]

/-- Fixing the dense algebraic image fixes the entire local Hilbert closure.
The smooth fixed-level map on that closure is the original inclusion. -/
theorem hasPlaceFixedSmoothRealization_of_ambient
    (hR : HasPlaceHilbertRealization (σ.comp i) j iK κ d W)
    (hiK : Continuous iK) (hne : W ≠ ⊥)
    (hfix : ∀ v : W, j v ∈ fixedSubspace τ U)
    (hs : ∀ v : W, Langlands.Archimedean.IsSmoothVector J σ (j v))
    (hinner : ∀ g x y, Inner.inner ℂ (σ g x) (σ g y) = Inner.inner ℂ x y)
    (p : A →* G) (c : A → A) (hcentral : ∀ g h, Commute (c g) (i h))
    (hsplit : ∀ g, c g * i (p g) = g) (hc : ContMDiff J J ∞ c)
    (hp : ContMDiff J I ∞ (p : A → G)) :
    HasPlaceFixedSmoothRealization (𝔞 := 𝔞) σ τ i j iK κ d hcomm U W := by
  obtain ⟨hplace, hW, hGK⟩ := hR
  refine ⟨hplace, hW, hGK, ?_⟩
  let R := placeClosureRepresentation (σ.comp i) j iK κ d hplace W hW
  let Q := LinearMap.range (j.comp W.subtype)
  let C := Q.topologicalClosure
  let : CompleteSpace C := Q.isClosed_topologicalClosure.completeSpace_coe
  have hsub : C ≤ fixedSubspace τ U := by
    apply closure_minimal _ (isClosed_fixedSubspace τ U)
    rintro _ ⟨v, rfl⟩
    exact hfix v
  let : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : W)
  exact exists_fixedDerivativeMap_of_gkHilbertRealization R σ τ i p c U iK hiK
    (PlaceComponent.restrictCompact hW) (PlaceComponent.restrictLie hW)
    (rangeClosureEmbedding (j.comp W.subtype)) hGK hinner hcomm
    hcentral hsplit hc hp C.subtypeL (fun _ _ => rfl) (fun v => hsub v.property) v₀ hv₀ (hs v₀)

end Langlands.Automorphic
