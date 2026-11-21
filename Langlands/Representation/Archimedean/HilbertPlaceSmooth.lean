import Langlands.Representation.Archimedean.GKHilbertClosure
import Langlands.Representation.Archimedean.SmoothFixedSubspace
import Langlands.Representation.Archimedean.SmoothIntertwinerExtension

/-! # Smooth comparison at a commuting fixed level -/

noncomputable section
open scoped ContDiff Manifold TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000

namespace Langlands.Archimedean

open DerivativeSmoothVectors SmoothInvariantSubspace
universe ua ub uG uA uK uL uV uE uH
attribute [local instance 100] LieRing.ofAssociativeRing

variable {𝔤 : Type ua} [NormedRing 𝔤] [NormedAlgebra ℝ 𝔤]
  {𝔞 : Type ub} [NormedAddCommGroup 𝔞] [NormedSpace ℝ 𝔞]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace 𝔤 G] [LieGroup 𝓘(ℝ, 𝔤) ∞ G]
  {A : Type uA} [Group A] [TopologicalSpace A] [ChartedSpace 𝔞 A] [LieGroup 𝓘(ℝ, 𝔞) ∞ A]
  {K : Type uK} [Group K] [TopologicalSpace K] {L : Type uL} [Group L]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (π : G →* (E →L[ℂ] E)) (σ : A →* (H →L[ℂ] H)) (τ : L →* (H →L[ℂ] H))
  (i : G →* A) (p : A →* G) (c : A → A) (U : Subgroup L)

local notation "I" => 𝓘(ℝ, 𝔤)
local notation "J" => 𝓘(ℝ, 𝔞)

/-- A bounded local intertwiner with fixed image induces a genuine smooth map to the
fixed Hilbert level, given a smooth commuting splitting and a nonzero smooth sample
in the algebraic part of its local Hilbert realization. -/
theorem exists_fixedDerivativeMap_of_gkHilbertRealization
    (iK : K →* G) (hiK : Continuous iK)
    (κ : Representation ℂ K V) (d : (ℂ ⊗[ℝ] 𝔤) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (j : V →ₗ[ℂ] E) (hGK : IsGKHilbertRealization iK κ d π j)
    (hunit : ∀ g x y, Inner.inner ℂ (σ g x) (σ g y) = Inner.inner ℂ x y)
    (hcomm : ∀ g l v, σ g (τ l v) = τ l (σ g v))
    (hcentral : ∀ g h, Commute (c g) (i h)) (hsplit : ∀ g, c g * i (p g) = g)
    (hc : ContMDiff J J ∞ c) (hp : ContMDiff J I ∞ (p : A → G))
    (T : E →L[ℂ] H) (hT : ∀ g v, T (π g v) = σ (i g) (T v))
    (hU : ∀ v, T v ∈ fixedSubspace τ U)
    (v₀ : V) (hv₀ : v₀ ≠ 0) (hs : IsSmoothVector J σ (T (j v₀))) :
    ∃ M : DerivativeSmoothVectors I π →L[ℂ]
        DerivativeSmoothVectors J (fixedRestriction τ U σ hcomm),
      ∀ v, ((toSmooth J (fixedRestriction τ U σ hcomm) (M v) : fixedSubspace τ U) : H) =
        T (toSmooth I π v) := by
  obtain ⟨hcont, hirr, hinner, hadm, hinj, -, hrec, -, hloc, -⟩ := hGK
  let x := j v₀
  have hx : x ≠ 0 := fun h => hv₀ (hinj (h.trans j.map_zero.symm))
  let z : ℂ := (↑‖x‖ : ℂ)⁻¹
  let x₀ := z • x
  have hnorm : ‖x₀‖ = 1 := by
    change ‖(↑‖x‖ : ℂ)⁻¹ • x‖ = 1
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg x)]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)
  have hfin : FiniteVectors.IsFiniteVector (linearRepresentation (π.comp iK)) x :=
    (hrec x).1 (LinearMap.mem_range_self j v₀)
  have hs₀ : IsSmoothVector I π x₀ := (smoothVectors I π).smul_mem z (hloc v₀)
  have hsT : IsSmoothVector J σ (T x₀) := by
    change IsSmoothVector J σ (T (z • x))
    rw [map_smul]
    exact (smoothVectors J σ).smul_mem z hs
  let P := fixedRestriction τ U σ hcomm
  let S : boundedIntertwiners π (P.comp i) :=
    ⟨T.codRestrict (fixedSubspace τ U) hU, fun g v => Subtype.ext (hT g v)⟩
  have hsS : IsSmoothVector J P (S.val x₀) :=
    (isSmoothVector_fixedRestriction_iff τ U σ hcomm J (S.val x₀)).2 hsT
  have hcontK : IsContinuousRepresentation (π.comp iK) :=
    hcont.comp ((hiK.comp continuous_fst).prodMk continuous_snd)
  have hunitK (g : G) (v w : fixedSubspace τ U) :
      Inner.inner ℂ ((P.comp i) g v) ((P.comp i) g w) = Inner.inner ℂ v w :=
    hunit (i g) (v : H) (w : H)
  obtain ⟨recover, hrecover⟩ := hilbertIntertwinerEvaluation G K iK E (fixedSubspace τ U)
    π (P.comp i) hcontK hadm ⟨x, hx, hfin⟩ hirr hinner hunitK x₀ hnorm
  exact ⟨SmoothIntertwinerExtension.derivativeMap π P i p c hcentral recover hrecover
    hc hp hsplit hs₀ S hsS, fun _ => rfl⟩

end Langlands.Archimedean
