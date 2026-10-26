import Langlands.Representation.Induction.CompactQuotientProof
import Langlands.Representation.Smooth.Contragredient.Definitions
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Conditional bilinear integration on smooth induction

The measure, integrability, and diagonal ambient right-translation invariance
are supplied explicitly. No existence or perfectness of the pairing is asserted.
-/

noncomputable section

open MeasureTheory

namespace Langlands.Induction

universe uG uV uW uV' uW'

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (P : Subgroup G) (τ : Representation ℂ P V) (υ : Representation ℂ P W)

/-- A bilinear coefficient pairing of actual smooth induced functions is locally constant. -/
theorem bilinearPairing_isLocallyConstant (b : W →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (h : SmoothFunctions P υ) (f : SmoothFunctions P τ) :
    IsLocallyConstant (fun x => b (eval P υ h x) (eval P τ f x)) :=
  (eval_isLocallyConstant P υ h).comp₂ (eval_isLocallyConstant P τ f)
    (fun w v => b w v)

/-- Integrate a supplied complex bilinear pairing, assuming all scalar integrands
are integrable for the supplied measure. -/
def integralBilinearPairing (b : W →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (K : Subgroup G) [MeasurableSpace K] (μ : Measure K)
    (hint : ∀ (h : SmoothFunctions P υ) (f : SmoothFunctions P τ),
      Integrable (fun k : K => b (eval P υ h k) (eval P τ f k)) μ) :
    SmoothFunctions P υ →ₗ[ℂ] SmoothFunctions P τ →ₗ[ℂ] ℂ where
  toFun h :=
    { toFun := fun f => ∫ k : K, b (eval P υ h k) (eval P τ f k) ∂μ
      map_add' := by
        intro f₁ f₂
        change (∫ k : K, b (eval P υ h k)
          (eval P τ f₁ k + eval P τ f₂ k) ∂μ) = _
        simp_rw [map_add]
        exact integral_add (hint h f₁) (hint h f₂)
      map_smul' := by
        intro c f
        change (∫ k : K, b (eval P υ h k) (c • eval P τ f k) ∂μ) = _
        simp_rw [map_smul]
        exact integral_smul c _ }
  map_add' := by
    intro h₁ h₂
    ext f
    change (∫ k : K, b (eval P υ h₁ k + eval P υ h₂ k) (eval P τ f k) ∂μ) = _
    simp_rw [map_add, LinearMap.add_apply]
    exact integral_add (hint h₁ f) (hint h₂ f)
  map_smul' := by
    intro c h
    ext f
    change (∫ k : K, b (c • eval P υ h k) (eval P τ f k) ∂μ) = _
    simp_rw [map_smul, LinearMap.smul_apply]
    exact integral_smul c _

omit [IsTopologicalGroup G] in
/-- Evaluation is the supplied scalar integral, with no conjugation. -/
theorem integralBilinearPairing_apply (b : W →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (K : Subgroup G) [MeasurableSpace K] (μ : Measure K)
    (hint : ∀ (h : SmoothFunctions P υ) (f : SmoothFunctions P τ),
      Integrable (fun k : K => b (eval P υ h k) (eval P τ f k)) μ)
    (h : SmoothFunctions P υ) (f : SmoothFunctions P τ) :
    integralBilinearPairing P τ υ b K μ hint h f =
      ∫ k : K, b (eval P υ h k) (eval P τ f k) ∂μ :=
  rfl

/-- Diagonal ambient right-translation invariance yields an intertwiner into the
full algebraic dual. The invariance is a hypothesis on the actual scalar integral. -/
def integralBilinearDualMap (b : W →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (K : Subgroup G) [MeasurableSpace K] (μ : Measure K)
    (hint : ∀ (h : SmoothFunctions P υ) (f : SmoothFunctions P τ),
      Integrable (fun k : K => b (eval P υ h k) (eval P τ f k)) μ)
    (hinv : ∀ (g : G) (h : SmoothFunctions P υ) (f : SmoothFunctions P τ),
      (∫ k : K, b (eval P υ h ((k : G) * g)) (eval P τ f ((k : G) * g)) ∂μ) =
        ∫ k : K, b (eval P υ h k) (eval P τ f k) ∂μ) :
    (smoothInduced P υ).IntertwiningMap (smoothInduced P τ).dual where
  toLinearMap := integralBilinearPairing P τ υ b K μ hint
  isIntertwining' g := by
    ext h f
    have hi := hinv g h (smoothInduced P τ g⁻¹ f)
    change (∫ k : K, b (eval P υ h ((k : G) * g)) (eval P τ f k) ∂μ) =
      ∫ k : K, b (eval P υ h k) (eval P τ f ((k : G) * g⁻¹)) ∂μ
    change (∫ k : K, b (eval P υ h ((k : G) * g))
      (eval P τ f (((k : G) * g) * g⁻¹)) ∂μ) =
      ∫ k : K, b (eval P υ h k) (eval P τ f ((k : G) * g⁻¹)) ∂μ at hi
    simpa only [mul_inv_cancel_right] using hi

/-- The same integral gives a map into the smooth contragredient. Its values are
smooth by equivariance and smoothness of the source, through `smoothLift`. -/
def integralBilinearSmoothDualMap (b : W →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (K : Subgroup G) [MeasurableSpace K] (μ : Measure K)
    (hint : ∀ (h : SmoothFunctions P υ) (f : SmoothFunctions P τ),
      Integrable (fun k : K => b (eval P υ h k) (eval P τ f k)) μ)
    (hinv : ∀ (g : G) (h : SmoothFunctions P υ) (f : SmoothFunctions P τ),
      (∫ k : K, b (eval P υ h ((k : G) * g)) (eval P τ f ((k : G) * g)) ∂μ) =
        ∫ k : K, b (eval P υ h k) (eval P τ f k) ∂μ) :
    (smoothInduced P υ).IntertwiningMap (smoothContragredient (smoothInduced P τ)) :=
  smoothLift (smoothInduced_smooth P υ) (integralBilinearDualMap P τ υ b K μ hint hinv)

/-- Evaluation of the smooth-dual map is the original bilinear integral. -/
theorem integralBilinearSmoothDualMap_apply (b : W →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (K : Subgroup G) [MeasurableSpace K] (μ : Measure K)
    (hint : ∀ (h : SmoothFunctions P υ) (f : SmoothFunctions P τ),
      Integrable (fun k : K => b (eval P υ h k) (eval P τ f k)) μ)
    (hinv : ∀ (g : G) (h : SmoothFunctions P υ) (f : SmoothFunctions P τ),
      (∫ k : K, b (eval P υ h ((k : G) * g)) (eval P τ f ((k : G) * g)) ∂μ) =
        ∫ k : K, b (eval P υ h k) (eval P τ f k) ∂μ)
    (h : SmoothFunctions P υ) (f : SmoothFunctions P τ) :
    smoothDualPairing (smoothInduced P τ)
      (integralBilinearSmoothDualMap P τ υ b K μ hint hinv h) f =
      ∫ k : K, b (eval P υ h k) (eval P τ f k) ∂μ :=
  rfl

section Compatibility

variable {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']
variable {W' : Type uW'} [AddCommGroup W'] [Module ℂ W']
variable (τ' : Representation ℂ P V') (υ' : Representation ℂ P W')

/-- Coefficient intertwiners preserving the pairings preserve the integrated
pairing, with the same subgroup and measure. -/
theorem integralBilinearPairing_map
    (b : W →ₗ[ℂ] V →ₗ[ℂ] ℂ) (b' : W' →ₗ[ℂ] V' →ₗ[ℂ] ℂ)
    (A : υ.IntertwiningMap υ') (B : τ.IntertwiningMap τ')
    (hb : ∀ (w : W) (v : V), b' (A w) (B v) = b w v)
    (K : Subgroup G) [MeasurableSpace K] (μ : Measure K)
    (hint : ∀ (h : SmoothFunctions P υ) (f : SmoothFunctions P τ),
      Integrable (fun k : K => b (eval P υ h k) (eval P τ f k)) μ)
    (hint' : ∀ (h : SmoothFunctions P υ') (f : SmoothFunctions P τ'),
      Integrable (fun k : K => b' (eval P υ' h k) (eval P τ' f k)) μ)
    (h : SmoothFunctions P υ) (f : SmoothFunctions P τ) :
    integralBilinearPairing P τ' υ' b' K μ hint'
      (smoothInducedMap P A h) (smoothInducedMap P B f) =
      integralBilinearPairing P τ υ b K μ hint h f := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun k => hb (eval P υ h k) (eval P τ f k)

/-- The smooth-dual maps satisfy the corresponding pullback square under actual
coefficient intertwiners preserving the pairings. -/
theorem integralBilinearSmoothDualMap_natural
    (b : W →ₗ[ℂ] V →ₗ[ℂ] ℂ) (b' : W' →ₗ[ℂ] V' →ₗ[ℂ] ℂ)
    (A : υ.IntertwiningMap υ') (B : τ.IntertwiningMap τ')
    (hb : ∀ (w : W) (v : V), b' (A w) (B v) = b w v)
    (K : Subgroup G) [MeasurableSpace K] (μ : Measure K)
    (hint : ∀ (h : SmoothFunctions P υ) (f : SmoothFunctions P τ),
      Integrable (fun k : K => b (eval P υ h k) (eval P τ f k)) μ)
    (hint' : ∀ (h : SmoothFunctions P υ') (f : SmoothFunctions P τ'),
      Integrable (fun k : K => b' (eval P υ' h k) (eval P τ' f k)) μ)
    (hinv : ∀ (g : G) (h : SmoothFunctions P υ) (f : SmoothFunctions P τ),
      (∫ k : K, b (eval P υ h ((k : G) * g)) (eval P τ f ((k : G) * g)) ∂μ) =
        ∫ k : K, b (eval P υ h k) (eval P τ f k) ∂μ)
    (hinv' : ∀ (g : G) (h : SmoothFunctions P υ') (f : SmoothFunctions P τ'),
      (∫ k : K, b' (eval P υ' h ((k : G) * g)) (eval P τ' f ((k : G) * g)) ∂μ) =
        ∫ k : K, b' (eval P υ' h k) (eval P τ' f k) ∂μ) :
    (contragredientMap (smoothInducedMap P B)).comp
      ((integralBilinearSmoothDualMap P τ' υ' b' K μ hint' hinv').comp
        (smoothInducedMap P A)) =
      integralBilinearSmoothDualMap P τ υ b K μ hint hinv := by
  ext h f
  exact integralBilinearPairing_map P τ υ τ' υ' b b' A B hb K μ hint hint' h f

end Compatibility

end Langlands.Induction
