import Langlands.Global.RankinSelberg.RealAdjacentConvergence
import Langlands.Global.RankinSelberg.RealAdjacentGodementUnfolding
import Langlands.Global.RankinSelberg.RealEqualDualConvergence

/-! # The paired real corank-one unfoldings on a right half-plane -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealJacquet

open Langlands.LocalFactor.Archimedean
open ArchimedeanLocal RealGodement RealEqualConvergence RealEqualDualConvergence

attribute [local instance] archimedeanEquationRealGLMeasurable
  archimedeanEquationRealGLBorel archimedeanEquationRealNMeasurable
  archimedeanEquationRealNBorel archimedeanEquationRealQMeasurable
  archimedeanEquationRealQBorel

variable {r : ℕ}

local notation "H" => Langlands.GeneralLinear (r + 1) ℝ
local notation "N" => GeneralLinear.upperUnipotent (r + 1) ℝ
local notation "ι" => GeneralLinear.inverseTranspose (r + 1) ℝ
local notation "w" => GeneralLinear.weylLong (r + 1) ℝ

/-- Inverse transpose preserves the real matrix height. -/
theorem realMatrixHeight_inverseTranspose {n : ℕ} (g : Langlands.GeneralLinear n ℝ) :
    realMatrixHeight (GeneralLinear.inverseTranspose n ℝ g) = realMatrixHeight g := by
  have h1 : ((GeneralLinear.inverseTranspose n ℝ g : Langlands.GeneralLinear n ℝ) :
      Matrix (Fin n) (Fin n) ℝ) = (g⁻¹).val.transpose := by
    rw [GeneralLinear.inverseTranspose_coe]
  have h2 : (((GeneralLinear.inverseTranspose n ℝ g)⁻¹ : Langlands.GeneralLinear n ℝ) :
      Matrix (Fin n) (Fin n) ℝ) = g.val.transpose := by
    rw [← map_inv, GeneralLinear.inverseTranspose_coe, inv_inv]
  unfold realMatrixHeight
  simp only [h1, h2, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => add_comm _ _

private theorem model_regular {ds : List RealBlock} {a : ℝˣ} {U : H → ℂ}
    (hU : U ∈ realUniformWhittakerModel r ds a) :
    U ∈ RealLocalWhittaker.regularFunctions r a :=
  (realUniformWhittakerRegularity r ds a U hU).1 []

private theorem model_gauge {ds : List RealBlock} {a : ℝˣ} {U : H → ℂ}
    (hU : U ∈ realUniformWhittakerModel r ds a) : HasGauge U :=
  RealWhittakerGauge.exists_gauge_bound (realUniformWhittakerRegularity r ds a U hU).1
    (realUniformWhittakerRegularity r ds a U hU).2

private theorem model_growth {ds : List RealBlock} {a : ℝˣ} {V : H → ℂ}
    (hV : V ∈ realUniformWhittakerModel r ds a) :
    ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ g, ‖V g‖ ≤ C * realMatrixHeight g ^ M := by
  obtain ⟨M, hM⟩ := (realUniformWhittakerRegularity r ds a V hV).2
  obtain ⟨C, hC, hb⟩ := hM []
  exact ⟨C, M, hC, hb⟩

private theorem dual_growth {V : H → ℂ}
    (hV : ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ g, ‖V g‖ ≤ C * realMatrixHeight g ^ M) :
    ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧
      ∀ g, ‖ArchimedeanLocal.dualFunction (r + 1) V g‖ ≤ C * realMatrixHeight g ^ M := by
  obtain ⟨C, M, hC, hb⟩ := hV
  refine ⟨C * realMatrixHeight w ^ M, M,
    mul_nonneg hC (pow_nonneg (RealPlaceRestriction.realMatrixHeight_nonneg _) _), fun g => ?_⟩
  change ‖V (w * ι g)‖ ≤ _
  calc
    ‖V (w * ι g)‖ ≤ C * realMatrixHeight (w * ι g) ^ M := hb _
    _ ≤ C * (realMatrixHeight w * realMatrixHeight g) ^ M := by
      gcongr
      · exact RealPlaceRestriction.realMatrixHeight_nonneg _
      · rw [← realMatrixHeight_inverseTranspose g]
        exact RealCharacterChange.realMatrixHeight_mul_le _ _
    _ = _ := by ring

private theorem pair_invariant {a : ℝˣ} {U V : H → ℂ}
    (hU : U ∈ RealLocalWhittaker.regularFunctions r (-a))
    (hV : V ∈ RealLocalWhittaker.regularFunctions r a) :
    ∀ u ∈ N, ∀ g z : H, U (u * g) * V (u * g * z) = U g * V (g * z) := by
  intro u hu g z
  rw [hU.1 u hu g, mul_assoc u g z, hV.1 u hu (g * z)]
  linear_combination (U g * V (g * z)) * realWhittakerCharacter_mul_neg a u

private theorem dual_translate (V : H → ℂ) (x z : H) :
    ArchimedeanLocal.dualFunction (r + 1) V (x * z) =
      ArchimedeanLocal.dualFunction (r + 1) (fun y => V (y * ι z)) x := by
  change V (w * ι (x * z)) = V (w * ι x * ι z)
  rw [map_mul, mul_assoc]

private theorem dual_pair_invariant {U V : H → ℂ}
    (hinv : ∀ u ∈ N, ∀ g z : H, U (u * g) * V (u * g * z) = U g * V (g * z)) :
    ∀ u ∈ N, ∀ g z : H,
      ArchimedeanLocal.dualFunction (r + 1) U (u * g) *
          ArchimedeanLocal.dualFunction (r + 1) V (u * g * z) =
        ArchimedeanLocal.dualFunction (r + 1) U g *
          ArchimedeanLocal.dualFunction (r + 1) V (g * z) := by
  intro u hu g z
  rw [dual_translate V (u * g) z, dual_translate V g z]
  exact dual_mul_invariant (W' := fun y => V (y * ι z)) (fun u hu g => hinv u hu g (ι z)) u hu g

/-- For uniform-model coefficients, both unfoldings of the separated real Godement
coefficient hold on a right half-plane, with no further integrability hypothesis. -/
def RealAdjacentGodementHalfPlaneStatement : Prop :=
  ∀ (D : RealQuotientMeasureData r) (a : ℝˣ) (c : RealCharacterData)
    (F : 𝓢(Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ, ℂ)) (f : 𝓢(Fin (r + 1) → ℝ, ℂ))
    (ds dds es : List RealBlock) (U V : Langlands.GeneralLinear (r + 1) ℝ → ℂ),
    U ∈ realUniformWhittakerModel r ds (-a) →
    ArchimedeanLocal.dualFunction (r + 1) U ∈ realUniformWhittakerModel r dds a →
    V ∈ realUniformWhittakerModel r es a →
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
    let Udual := ArchimedeanLocal.dualFunction (r + 1) U
    let Vdual := ArchimedeanLocal.dualFunction (r + 1) V
    let W := realAdjacentGodementCoefficient D a (realColumnProduct F f) U c
    let η := c.character.toMonoidHom
    let ηd := c.inverse.character.toMonoidHom
    let fF := realRowSchwartzFourier (r + 1) a f
    let FF := realRectangularSchwartzFourier a F
    let b := realAdjacentWeylSign r c
    realUnequalIntegral (Nat.lt_succ_self r) D W V s = b * realAdjacentUnfoldedIntegral D η F fF U V s ∧
    realUnequalDualIntegral (Nat.lt_succ_self r) (-a) D W V s =
      ((c.character ((-1 : ℝˣ) ^ (r + 1)) : ℂ) * b) *
        realAdjacentUnfoldedIntegral D ηd FF f Udual Vdual s

theorem realAdjacentGodementHalfPlane : RealAdjacentGodementHalfPlaneStatement (r := r) := by
  intro D a c F f ds dds es U V hU hUd hV
  have hUr := model_regular hU
  have hUdr := model_regular hUd
  have hVr := model_regular hV
  have hinv := pair_invariant hUr hVr
  obtain ⟨σ₁, h₁⟩ := realAdjacentConvergence (r := r) D c F (realRowSchwartzFourier (r + 1) a f) U V
    hUr.2.1.continuous hVr.2.1.continuous (SchwartzMap.continuous _) (hasRapidDecay_schwartz _)
    hinv (model_gauge hU) (model_growth hV)
  obtain ⟨σ₂, h₂⟩ := realAdjacentConvergence (r := r) D c.inverse (realRectangularSchwartzFourier a F) f
    (ArchimedeanLocal.dualFunction (r + 1) U) (ArchimedeanLocal.dualFunction (r + 1) V)
    hUdr.2.1.continuous (continuous_dual hVr.2.1.continuous) (SchwartzMap.continuous _)
    (hasRapidDecay_schwartz _) (dual_pair_invariant hinv) (model_gauge hUd)
    (dual_growth (model_growth hV))
  refine ⟨max σ₁ σ₂, fun s hs => ?_⟩
  exact realAdjacentGodementUnfolding D a c F f ds dds es U V hU hUd hV s
    (h₁ s ((le_max_left _ _).trans_lt hs)) (h₂ s ((le_max_right _ _).trans_lt hs))

end Langlands.Global.RankinSelbergGlobal.RealJacquet
