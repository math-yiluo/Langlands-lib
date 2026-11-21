import Langlands.Global.RankinSelberg.RealGodementColumnProduct
import Langlands.Global.RankinSelberg.RealLocalAdjacentIntegrals

/-! # Paired real corank-one unfoldings of separated Godement coefficients -/

noncomputable section

open Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealJacquet

open ArchimedeanLocal RealGodement

attribute [local instance] archimedeanEquationRealGLMeasurable
  archimedeanEquationRealGLBorel archimedeanEquationRealNMeasurable
  archimedeanEquationRealNBorel archimedeanEquationRealQMeasurable
  archimedeanEquationRealQBorel

variable {r : ℕ}
local notation "m" => (r + 1)
local notation "G" => Langlands.GeneralLinear (r + 2) ℝ
local notation "H" => Langlands.GeneralLinear (r + 1) ℝ
local notation "N" => GeneralLinear.upperUnipotent (r + 1) ℝ
local notation "M" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "R" => (Fin (r + 1) → ℝ)
local notation "X" => Matrix (Fin (r + 1)) (Fin (r + 2)) ℝ
local notation "Ud" => ArchimedeanLocal.dualFunction (r + 1)
local notation "Wd" => ArchimedeanLocal.dualFunction (r + 2)

private theorem model_left_law {ds : List RealBlock} {a : ℝˣ} {U : H → ℂ}
    (hU : U ∈ realUniformWhittakerModel r ds a) (u : N) (g : H) :
    U (u.val * g) = realWhittakerCharacter a u.val * U g := by
  have h := (realUniformWhittakerRegularity r ds a U hU).1 []
  exact h.1 u.val u.property g

private theorem left_law_dual (a : ℝˣ) (U : H → ℂ)
    (hU : ∀ (u : N) g, U (u.val * g) = realWhittakerCharacter a u.val * U g)
    (u : N) (g : H) :
    Ud U (u.val * g) = realWhittakerCharacter (-a) u.val * Ud U g := by
  change U (GeneralLinear.weylInverseTranspose m ℝ (u.val * g)) =
    realWhittakerCharacter (-a) u.val * U (GeneralLinear.weylInverseTranspose m ℝ g)
  rw [Langlands.Whittaker.weylInverseTranspose_left_unipotent, hU,
    RealUnequalPairConvergence.realWhittakerCharacter_reflected]

private theorem product_invariant (a : ℝˣ) (U V : H → ℂ)
    (hU : ∀ (u : N) g, U (u.val * g) = realWhittakerCharacter a u.val * U g)
    (hV : ∀ (u : N) g, V (u.val * g) = realWhittakerCharacter (-a) u.val * V g)
    (z : H) (u : N) (g : H) : U (u.val * g) * V ((u.val * g) * z) = U g * V (g * z) := by
  rw [mul_assoc, hU, hV, mul_mul_mul_comm]
  have hc : realWhittakerCharacter a u.val * realWhittakerCharacter (-a) u.val = 1 := by
    change (Langlands.Whittaker.standardCharacter (realScaledCharacter a) r u : ℂ) *
      (Langlands.Whittaker.standardCharacter (realScaledCharacter (-a)) r u : ℂ) = 1
    rw [standardCharacter_realScaled_neg, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hc, one_mul]

private theorem WeylSign_inverse (c : RealCharacterData) :
    realAdjacentWeylSign r c.inverse = realAdjacentWeylSign r c := by
  have hh (n : ℕ) : detCharacter c.inverse.character.toMonoidHom (GeneralLinear.weylLong n ℝ) =
      detCharacter c.character.toMonoidHom (GeneralLinear.weylLong n ℝ) := by
    have hw : (GeneralLinear.determinant (GeneralLinear.weylLong n ℝ))⁻¹ =
        GeneralLinear.determinant (GeneralLinear.weylLong n ℝ) := by
      rw [← map_inv, GeneralLinear.weylLong_inv]
    change (((c.character (GeneralLinear.determinant (GeneralLinear.weylLong n ℝ)))⁻¹ : ℂˣ) : ℂ) =
      ((c.character (GeneralLinear.determinant (GeneralLinear.weylLong n ℝ)) : ℂˣ) : ℂ)
    rw [← map_inv, hw]
  unfold realAdjacentWeylSign
  rw [hh, hh]

private theorem dual_realAdjacentGodementCoefficient (D : RealQuotientMeasureData r) (a : ℝˣ)
    (Φ : 𝓢(X, ℂ)) (c : RealCharacterData) (ds dds : List RealBlock) (U : H → ℂ)
    (hU : U ∈ realUniformWhittakerModel r ds (-a))
    (hUd : Ud U ∈ realUniformWhittakerModel r dds a) (g : G) :
    Wd (realAdjacentGodementCoefficient D a Φ U c) g =
    (c.character ((-1 : ℝˣ) ^ m) : ℂ) *
      realAdjacentGodementCoefficient D (-a) (realRectangularSchwartzFourier a Φ) (Ud U) c.inverse g := by
  let w := GeneralLinear.weylLong (r + 2) ℝ
  have h := (realGodementColumnReflection r D a Φ c ds dds U (w * g) hU hUd).2.2
  have he : GeneralLinear.weylInverseTranspose (r + 2) ℝ (w * g) =
      GeneralLinear.inverseTranspose (r + 2) ℝ g := by
    simp only [w, GeneralLinear.weylInverseTranspose_apply, map_mul, GeneralLinear.inverseTranspose_weylLong,
      ← mul_assoc, GeneralLinear.weylLong_mul_self, one_mul]
  rw [he] at h
  change godementColumnValue D a Φ U c (w * (w * GeneralLinear.inverseTranspose (r + 2) ℝ g)) = _
  rwa [← mul_assoc, GeneralLinear.weylLong_mul_self, one_mul]

/-- The exact primal and dual corank-one integrals for a separated Godement coefficient,
written as smaller equal-rank integrals against the corresponding matrix tests. -/
def RealAdjacentGodementUnfoldingStatement (r : ℕ) : Prop :=
  ∀ (D : RealQuotientMeasureData r) (a : ℝˣ) (c : RealCharacterData)
    (F : 𝓢(Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ, ℂ)) (f : 𝓢(Fin (r + 1) → ℝ, ℂ))
    (ds dds es : List RealBlock) (U V : Langlands.GeneralLinear (r + 1) ℝ → ℂ),
    U ∈ realUniformWhittakerModel r ds (-a) →
    ArchimedeanLocal.dualFunction (r + 1) U ∈ realUniformWhittakerModel r dds a →
    V ∈ realUniformWhittakerModel r es a →
    ∀ s : ℂ,
    let Udual := ArchimedeanLocal.dualFunction (r + 1) U
    let Vdual := ArchimedeanLocal.dualFunction (r + 1) V
    let W := realAdjacentGodementCoefficient D a (realColumnProduct F f) U c
    let η := c.character.toMonoidHom
    let ηd := c.inverse.character.toMonoidHom
    let fF := realRowSchwartzFourier (r + 1) a f
    let FF := realRectangularSchwartzFourier a F
    let b := realAdjacentWeylSign r c
    Integrable (realAdjacentUnfoldedKernel η F fF U V s) (D.measure.prod D.groupHaar) →
    Integrable (realAdjacentUnfoldedKernel ηd FF f Udual Vdual s) (D.measure.prod D.groupHaar) →
    realUnequalIntegral (Nat.lt_succ_self r) D W V s = b * realAdjacentUnfoldedIntegral D η F fF U V s ∧
    realUnequalDualIntegral (Nat.lt_succ_self r) (-a) D W V s =
      ((c.character ((-1 : ℝˣ) ^ (r + 1)) : ℂ) * b) *
        realAdjacentUnfoldedIntegral D ηd FF f Udual Vdual s

theorem realAdjacentGodementUnfolding : RealAdjacentGodementUnfoldingStatement r := by
  intro D a c F f ds dds es U V hU hUd hV s Udual Vdual W η ηd fF FF b hInt hIntd
  have hUlaw := model_left_law hU
  have hVlaw := model_left_law hV
  have hVlaw' : ∀ (u : N) g, V (u.val * g) = realWhittakerCharacter (-(-a)) u.val * V g := by
    simpa only [neg_neg] using hVlaw
  have hInv := product_invariant (-a) U V hUlaw hVlaw'
  have hInvd := product_invariant a Udual Vdual (model_left_law hUd) (left_law_dual a V hVlaw)
  have hSep (A : M) (v : R) : realColumnProduct F f (joinLastColumn A v) = F A * f v := by simp
  have hSepd (A : M) (v : R) : realColumnProduct FF fF (joinLastColumn A v) = FF A * fF v := by simp
  have hW (g : H) : W (padGL (Nat.succ_le_succ (Nat.le_succ r)) g) =
      b * ∫ k, realAdjacentRestrictionKernel η F fF U g k ∂D.groupHaar := by
    have h := realAdjacentGodementRestriction (r := r) D a c (realColumnProduct F f) F f hSep U g
    simpa only [W, b, η, fF, show (⇑(realRowSchwartzFourier m a f)) = realFourierTransform a f from
      funext (realRowSchwartzFourier_apply m a f)] using h
  have hWd (g : H) : Wd W (padGL (Nat.succ_le_succ (Nat.le_succ r)) g) =
      ((c.character ((-1 : ℝˣ) ^ m) : ℂ) * b) *
        ∫ k, realAdjacentRestrictionKernel ηd FF f Udual g k ∂D.groupHaar := by
    dsimp only [W]
    rw [dual_realAdjacentGodementCoefficient D a _ c ds dds U hU hUd, realColumnProduct_fourier]
    rw [realAdjacentGodementRestriction (r := r) D (-a) c.inverse (realColumnProduct FF fF) FF fF hSepd,
      WeylSign_inverse, mul_assoc]
    have hrow : realFourierTransform (-a) (fF : R → ℂ) = f := by
      rw [← funext (realRowSchwartzFourier_apply m (-a) fF)]
      exact congrArg (fun f : 𝓢(R, ℂ) => (f : R → ℂ)) (realRowSchwartzFourier_neg_comp m a f)
    rw [hrow]
  refine ⟨realLocalAdjacentUnfolding D η F fF W U V hInv b hW s hInt, ?_⟩
  rw [realUnequalDualIntegral_adjacent]
  exact realLocalAdjacentUnfolding D ηd FF f (Wd W) Udual Vdual hInvd _ hWd s hIntd

end Langlands.Global.RankinSelbergGlobal.RealJacquet
