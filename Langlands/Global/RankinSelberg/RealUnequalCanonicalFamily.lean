import Langlands.Global.RankinSelberg.RealUnequalDualFamily
import Langlands.Global.RankinSelberg.RealGodementCanonicalCoefficient

/-! # The real unequal-rank integrals along holomorphic families of regular Whittaker functions -/

noncomputable section

open MeasureTheory Metric Set
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealUnequalFamily

open ArchimedeanLocal RealEqualConvergence
open RealLocalWhittaker (iteratedRightDerivative regularFunctions)
open RealGodementProfiles (IsCompactProfile standardSection standardSection_mem)

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable
  archimedeanRealQBorel

variable {r t : ℕ}
local notation "GT" => Langlands.GeneralLinear (t + 1) ℝ
local notation "GR" => Langlands.GeneralLinear (r + 1) ℝ

/-- A uniform gauge passes to a reparametrized family whose parameters stay in the original
set. -/
theorem HasUniformGauge.comp {n : ℕ} {P Q : Type*} {S : Set P} {T : Set Q}
    {W : P → Langlands.GeneralLinear (n + 1) ℝ → ℂ} (hW : HasUniformGauge S W) (f : Q → P)
    (hf : ∀ u ∈ T, f u ∈ S) : HasUniformGauge T (fun u => W (f u)) := by
  obtain ⟨N, hN⟩ := hW
  refine ⟨N, fun M => ?_⟩
  obtain ⟨C, hC, hb⟩ := hN M
  exact ⟨C, hC, fun u hu => hb (f u) (hf u hu)⟩

/-- The exact ordinary and dual unequal-rank integrals for a holomorphic family of regular
larger Whittaker functions with locally uniform derivative growth, composed with a holomorphic
map of one complex variable, and a fixed regular smaller function: on every parameter disk
there is a common right half-plane of absolute convergence and joint holomorphy, with bounds
on closed vertical strips that are uniform over the disk. -/
def RealUnequalRegularFamilyBoundsStatement : Prop :=
  ∀ (h : t < r) (a b : ℝˣ) (D : RealQuotientMeasureData t) (m : ℕ)
    (W : (Fin m → ℂ) → GR → ℂ),
    (∀ z Xs, iteratedRightDerivative r Xs (W z) ∈ regularFunctions r a) →
    RealGodement.HasLocallyUniformDerivativeGrowth univ W →
    (∀ g, Differentiable ℂ (fun z => W z g)) →
    ∀ (p : ℂ → Fin m → ℂ), Differentiable ℂ p →
    ∀ V : GT → ℂ, (∀ Xs, iteratedRightDerivative t Xs V ∈ regularFunctions t (-a)) →
    (∃ N : ℕ, ∀ Xs, ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
      ‖iteratedRightDerivative t Xs V g‖ ≤ C * realMatrixHeight g ^ N) →
    ∀ R : ℝ, ∃ σ : ℝ,
      (∀ z ∈ ball (0 : ℂ) R, ∀ s : ℂ, σ < s.re →
        Integrable (realUnequalIntegrand h (W (p z)) V s) D.measure ∧
        Integrable (realUnequalDualKernel h (W (p z)) V s)
          (realUnequalDualMeasure (r := r) b D)) ∧
      DifferentiableOn ℂ (fun u : ℂ × ℂ => realUnequalIntegral h D (W (p u.1)) V u.2)
        (ball 0 R ×ˢ {s : ℂ | σ < s.re}) ∧
      DifferentiableOn ℂ (fun u : ℂ × ℂ => realUnequalDualIntegral h b D (W (p u.1)) V u.2)
        (ball 0 R ×ˢ {s : ℂ | σ < s.re}) ∧
      ∀ x y : ℝ, σ < x → ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ ball (0 : ℂ) R, ∀ s : ℂ,
        x ≤ s.re → s.re ≤ y →
        ‖realUnequalIntegral h D (W (p z)) V s‖ ≤ C ∧
        ‖realUnequalDualIntegral h b D (W (p z)) V s‖ ≤ C

theorem realUnequalRegularFamilyBounds :
    RealUnequalRegularFamilyBoundsStatement (r := r) (t := t) := by
  intro h a b D m W hreg hgrowth hdiff p hp V hregV hgrowthV R
  let T : Set (ℂ × ℂ) := ball 0 R ×ˢ univ
  let F (u : ℂ × ℂ) : GR → ℂ := W (p u.1)
  let B (_ : ℂ × ℂ) : GT → ℂ := V
  have hT : IsOpen T := isOpen_ball.prod isOpen_univ
  have hFχ (u : ℂ × ℂ) : HasLeftCharacter a (F u) := (hreg (p u.1) []).1
  have hBχ (u : ℂ × ℂ) : HasLeftCharacter (-a) (B u) := (hregV []).1
  have hFc (u : ℂ × ℂ) : Continuous (F u) := (hreg (p u.1) []).2.1.continuous
  have hBc (u : ℂ × ℂ) : Continuous (B u) := (hregV []).2.1.continuous
  have hFd (g : GR) : DifferentiableOn ℂ (F · g) T :=
    (((hdiff g).comp hp).comp differentiable_fst).differentiableOn
  have hBd (g : GT) : DifferentiableOn ℂ (B · g) T := differentiableOn_const (V g)
  have hK : IsCompact (p '' closedBall (0 : ℂ) R) :=
    (isCompact_closedBall (0 : ℂ) R).image hp.continuous
  obtain ⟨N, hN⟩ := exists_uniform_derivativeGrowth hgrowth hK (subset_univ _)
  have hFb : HasUniformGauge T F :=
    (hasUniformGauge_of_derivativeGrowth (p '' closedBall (0 : ℂ) R) W
      (fun z _ Xs => hreg z Xs) hN).comp (fun u : ℂ × ℂ => p u.1)
      (fun u hu => mem_image_of_mem p (ball_subset_closedBall hu.1))
  have hgV : HasGauge V := RealWhittakerGauge.exists_gauge_bound hregV hgrowthV
  have hBb : HasUniformGauge T B := hasUniformGauge_const T hgV
  obtain ⟨σ, hσ, hZo⟩ := realUnequalOrdinaryFamily (E := ℂ × ℂ) (a := a) h D T F B Prod.snd hT
    differentiable_snd hFχ hBχ hFc hBc hFd hBd hFb hBb
  obtain ⟨τ, hτ, hZd⟩ := realUnequalDualFamily (E := ℂ × ℂ) (a := a) h D b T F B Prod.snd hT
    differentiable_snd hFχ hBχ hFc hBc hFd hBd hFb hBb
  obtain ⟨σ₀, hOrdDom⟩ := ordinary_halfPlaneDomination h D T F B Prod.snd hFχ hBχ hFb hBb
  obtain ⟨τ₀, hDualDom⟩ := dual_halfPlaneDomination h D b T F B Prod.snd hFχ hBχ hFb hBb
  let S₀ := max (max σ τ) (max σ₀ τ₀)
  have hσ₀ : σ ≤ S₀ := (le_max_left _ _).trans (le_max_left _ _)
  have hτ₀ : τ ≤ S₀ := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨S₀, fun z hz s hs => ?_, ?_, ?_, ?_⟩
  · exact ⟨hσ (z, s) ⟨⟨hz, mem_univ s⟩, hσ₀.trans_lt hs⟩,
      hτ (z, s) ⟨⟨hz, mem_univ s⟩, hτ₀.trans_lt hs⟩⟩
  · exact hZo.mono fun u hu => ⟨⟨hu.1, mem_univ u.2⟩, hσ₀.trans_lt hu.2⟩
  · exact hZd.mono fun u hu => ⟨⟨hu.1, mem_univ u.2⟩, hτ₀.trans_lt hu.2⟩
  · intro x y hxy
    obtain ⟨M, hM, hDom⟩ := hOrdDom y
    obtain ⟨Md, hMd, hDomd⟩ := hDualDom y
    let C := ∫ u, ‖M u‖ ∂D.measure
    let Cd := ∫ u, ‖Md u‖ ∂realUnequalDualMeasure (r := r) b D
    refine ⟨max C Cd, (integral_nonneg fun _ => norm_nonneg _).trans (le_max_left _ _), ?_⟩
    intro z hz s hs ht
    have hS : S₀ < s.re := hxy.trans_le hs
    have hzT : (z, s) ∈ T := ⟨hz, mem_univ s⟩
    have hOrdσ : σ₀ < s.re := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hS
    have hDualτ : τ₀ < s.re := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hS
    constructor
    · apply le_trans _ (le_max_left C Cd)
      apply norm_integral_le_of_norm_le hM.norm
      exact ae_of_all _ fun u => (hDom (z, s) hzT hOrdσ ht u).trans (le_abs_self _)
    · apply le_trans _ (le_max_right C Cd)
      rw [dualIntegral_eq_prod h D b (W (p z)) V s (hτ (z, s) ⟨hzT, hτ₀.trans_lt hS⟩)]
      apply norm_integral_le_of_norm_le hMd.norm
      exact ae_of_all _ fun u => (hDomd (z, s) hzT hDualτ ht u).trans (le_abs_self _)

/-- The canonical continued Jacquet values of a fixed compact profile, as the inducing
exponents vary holomorphically with one complex parameter, against a fixed regular smaller
function. The canonical map for `-a` has left character `a`. -/
def RealUnequalCanonicalFamilyBoundsStatement : Prop :=
  ∀ (h : t < r) (a b : ℝˣ) (D : RealQuotientMeasureData t) (pr : Fin (r + 1) → Fin 2)
    (φ : Matrix.unitaryGroup (Fin (r + 1)) ℝ → ℂ) (hφ : IsCompactProfile pr φ)
    (p : ℂ → Fin (r + 1) → ℂ), Differentiable ℂ p →
    ∀ V : GT → ℂ, (∀ Xs, iteratedRightDerivative t Xs V ∈ regularFunctions t (-a)) →
    (∃ N : ℕ, ∀ Xs, ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
      ‖iteratedRightDerivative t Xs V g‖ ≤ C * realMatrixHeight g ^ N) →
    ∀ R : ℝ,
    let W (z : ℂ) := RealGodement.canonicalJacquetMap (-a) pr (p z)
      ⟨standardSection (p z) φ, standardSection_mem hφ (p z)⟩
    ∃ σ : ℝ,
      (∀ z ∈ ball (0 : ℂ) R, ∀ s : ℂ, σ < s.re →
        Integrable (realUnequalIntegrand h (W z) V s) D.measure ∧
        Integrable (realUnequalDualKernel h (W z) V s)
          (realUnequalDualMeasure (r := r) b D)) ∧
      DifferentiableOn ℂ (fun u : ℂ × ℂ => realUnequalIntegral h D (W u.1) V u.2)
        (ball 0 R ×ˢ {s : ℂ | σ < s.re}) ∧
      DifferentiableOn ℂ (fun u : ℂ × ℂ => realUnequalDualIntegral h b D (W u.1) V u.2)
        (ball 0 R ×ˢ {s : ℂ | σ < s.re}) ∧
      ∀ x y : ℝ, σ < x → ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ ball (0 : ℂ) R, ∀ s : ℂ,
        x ≤ s.re → s.re ≤ y →
        ‖realUnequalIntegral h D (W z) V s‖ ≤ C ∧
        ‖realUnequalDualIntegral h b D (W z) V s‖ ≤ C

theorem realUnequalCanonicalFamilyBounds :
    RealUnequalCanonicalFamilyBoundsStatement (r := r) (t := t) := by
  intro h a b D pr φ hφ p hp V hregV hgrowthV R
  have hJ := RealGodement.canonicalJacquetFamily_properties (-a) hφ
  have hreg (z : Fin (r + 1) → ℂ) (Xs) :
      iteratedRightDerivative r Xs (RealGodement.canonicalJacquetFamily (-a) hφ z) ∈
        regularFunctions r a := by
    simpa only [neg_neg] using hJ.1 z Xs
  have key := realUnequalRegularFamilyBounds h a b D (r + 1)
    (RealGodement.canonicalJacquetFamily (-a) hφ) hreg hJ.2.1 (fun g => hJ.2.2.1 [] g)
    p hp V hregV hgrowthV R
  intro W
  have hW : W = fun z => RealGodement.canonicalJacquetFamily (-a) hφ (p z) :=
    funext fun z => RealGodement.canonicalJacquetMap_standardSection (-a) hφ (p z)
  rw [hW]
  exact key

end Langlands.Global.RankinSelbergGlobal.RealUnequalFamily
