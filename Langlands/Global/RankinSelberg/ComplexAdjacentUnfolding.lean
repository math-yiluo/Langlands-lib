import Langlands.Analysis.Local.QuotientRightShear
import Langlands.Global.RankinSelberg.ComplexGodementSection
import Langlands.Global.RankinSelberg.ComplexLocalEqualQuotientChange
import Langlands.Global.RankinSelberg.EqualIntegrandProducts

/-! # Unfolding the adjacent-rank complex integral with a split Godement test -/

noncomputable section

open MeasureTheory Topology
open scoped Matrix.Norms.Operator NNReal

namespace Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding

open ArchimedeanLocal (ComplexQuotientMeasureData complexNormalizedAbs complexUnequalIntegrand
  complexUnequalIntegral)
open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean Langlands.QuotientIntegration
open Langlands.RankinSelberg (LeftUnipotentQuotient unipotent_det)
open ComplexGodement (characterWeight normPower)
open ComplexCharacterChange (whittakerCharacter_neg_parameter)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear r.succ ℂ
local notation "G'" => Langlands.GeneralLinear r.succ.succ ℂ
local notation "N" => Langlands.GeneralLinear.upperUnipotent r.succ ℂ
local notation "Q" => LeftUnipotentQuotient r ℂ
local notation "Mat" => Matrix (Fin r.succ) (Fin r.succ) ℂ
local notation "Vec" => Fin r.succ → ℂ

local instance adjacentGLSecondCountable (r : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear r.succ ℂ) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology

private abbrev detNormPower (s : ℂ) (g : G) : ℂ := normPower s (determinant g)

private theorem detPower_eq (s : ℂ) (g : G) :
    ArchimedeanLocal.detPower complexNormalizedAbs g s = detNormPower s g := by
  let A := complexNormalizedAbs g.val.det
  have hA : 0 < A := pow_pos (norm_pos_iff.mpr g.det_ne_zero) _
  change Complex.exp (s * (Real.log A : ℂ)) = (A : ℂ) ^ s
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hA.ne'),
    ← Complex.ofReal_log hA.le, mul_comm]

private theorem power_add (p s : ℂ) (g : G) :
    detNormPower (p + s) g = detNormPower p g * detNormPower s g := by
  simp only [← detPower_eq, ArchimedeanLocal.detPower, add_mul, Complex.exp_add]

private theorem weight_add (d : ComplexCharacterData) (p s : ℂ) (g : G) :
    characterWeight d (p + s) (determinant g) =
      characterWeight d p (determinant g) * detNormPower s g := by
  change (d.character (determinant g) : ℂ) * detNormPower (p + s) g =
    ((d.character (determinant g) : ℂ) * detNormPower p g) * detNormPower s g
  rw [power_add, mul_assoc]

private theorem detNormPower_unipotent_mul (u : N) (g : G) (s : ℂ) :
    detNormPower s (u.val * g) = detNormPower s g := by
  have h : determinant u.val = 1 := Units.ext (unipotent_det u)
  change normPower s (determinant (u.val * g)) = _
  simp only [map_mul, h, one_mul]

private theorem detNormPower_mul (s : ℂ) (g h : G) :
    detNormPower s (g * h) = detNormPower s g * detNormPower s h := by
  change normPower s (determinant (g * h)) = _
  simp only [map_mul]

/-- The double kernel in Jacquet's unfolded adjacent-rank integral. Its `h` factor is
square Godement weight, and its quotient factor is the smaller equal-rank kernel. -/
def unfoldedKernel (d : ComplexCharacterData) (p s : ℂ) (Φ : Mat → ℂ) (φ : Vec → ℂ)
    (W V : G → ℂ) (x : G × Q) : ℂ :=
  Φ x.1.val * characterWeight d (p + s) (determinant x.1) *
    ArchimedeanLocal.equalIntegrand complexNormalizedAbs W (fun g => V (g * x.1)) φ s x.2

private def intermediateRaw (d : ComplexCharacterData) (p s : ℂ) (Φ : Mat → ℂ) (φ : Vec → ℂ)
    (W V : G → ℂ) (h g : G) : ℂ :=
  Φ h.val * characterWeight d p (determinant h) *
    (W (g * h⁻¹) * V g * φ (Langlands.RankinSelberg.lastRow (g * h⁻¹)) * detNormPower s g)

private def intermediateKernel (d : ComplexCharacterData) (p s : ℂ) (Φ : Mat → ℂ) (φ : Vec → ℂ)
    (W V : G → ℂ) (x : G × Q) : ℂ :=
  intermediateRaw d p s Φ φ W V x.1 x.2.out

private theorem opposing_characters_mul {a : ℂˣ} (W V : G → ℂ)
    (hW : ∀ (u : N) g, W (u.val * g) = complexWhittakerCharacter a u.val * W g)
    (hV : ∀ (u : N) g, V (u.val * g) = complexWhittakerCharacter (-a) u.val * V g)
    (u : N) (g h : G) : W (u.val * g) * V (u.val * h) = W g * V h := by
  rw [hW, hV, mul_mul_mul_comm, whittakerCharacter_neg_parameter, one_mul]

private theorem intermediateKernel_mk (d : ComplexCharacterData) (p s : ℂ) (Φ : Mat → ℂ)
    (φ : Vec → ℂ) (W V : G → ℂ) {a : ℂˣ}
    (hW : ∀ (u : N) g, W (u.val * g) = complexWhittakerCharacter a u.val * W g)
    (hV : ∀ (u : N) g, V (u.val * g) = complexWhittakerCharacter (-a) u.val * V g) (h g : G) :
    intermediateKernel d p s Φ φ W V (h, leftQuotientMap N g) = intermediateRaw d p s Φ φ W V h g := by
  have hi (u : N) (x : G) : intermediateRaw d p s Φ φ W V h (u.val * x) =
      intermediateRaw d p s Φ φ W V h x := by
    unfold intermediateRaw
    rw [mul_assoc u.val x h⁻¹, opposing_characters_mul W V hW hV,
      Langlands.RankinSelberg.lastRow_unipotent_mul, detNormPower_unipotent_mul]
  exact congrArg (descend N (intermediateRaw d p s Φ φ W V h) hi)
    (Quotient.out_eq (leftQuotientMap N g))

private theorem unfolded_eq_comp_shear (d : ComplexCharacterData) (p s : ℂ) (Φ : Mat → ℂ)
    (φ : Vec → ℂ) (W V : G → ℂ) {a : ℂˣ}
    (hW : ∀ (u : N) g, W (u.val * g) = complexWhittakerCharacter a u.val * W g)
    (hV : ∀ (u : N) g, V (u.val * g) = complexWhittakerCharacter (-a) u.val * V g) :
    intermediateKernel d p s Φ φ W V ∘ rightShear N = unfoldedKernel d p s Φ φ W V := by
  funext x
  obtain ⟨h, q⟩ := x
  refine Quotient.inductionOn q fun g => ?_
  have hpair (u : N) (y : G) : W (u.val * y) * V (u.val * y * h) = W y * V (y * h) := by
    rw [mul_assoc, opposing_characters_mul W V hW hV]
  have hg : (g * h) * h⁻¹ = g := by rw [mul_assoc, mul_inv_cancel, mul_one]
  change intermediateKernel d p s Φ φ W V (h, leftQuotientMap N (g * h)) = _
  rw [intermediateKernel_mk d p s Φ φ W V hW hV, intermediateRaw, unfoldedKernel,
    EqualIntegrandProducts.equalIntegrand_mk_of_pair_invariant complexNormalizedAbs r W
      (fun y => V (y * h)) hpair φ s g, detPower_eq, hg, weight_add, detNormPower_mul]
  ring

private theorem unfold_inner (ν : Measure G) [ν.IsMulRightInvariant] (d : ComplexCharacterData)
    (p s : ℂ) (Φ : Mat → ℂ) (φ : Vec → ℂ) (W V : G → ℂ) (g : G) (c : ℂ) :
    (c * characterWeight d (p + 1 / 2) (determinant g) *
        (∫ h, Φ (h * g).val * φ (Langlands.RankinSelberg.lastRow h⁻¹) * W h⁻¹ *
          characterWeight d p (determinant h) ∂ν)) * V g * detNormPower (s - 1 / 2) g =
      c * ∫ h, intermediateRaw d p s Φ φ W V h g ∂ν := by
  let F (h : G) := Φ (h * g).val * φ (Langlands.RankinSelberg.lastRow h⁻¹) * W h⁻¹ * characterWeight d p (determinant h)
  let I (h : G) := (characterWeight d (p + 1 / 2) (determinant g) * F h) * V g *
    detNormPower (s - 1 / 2) g
  have hdet : characterWeight d (p + 1 / 2) (determinant g) * detNormPower (s - 1 / 2) g =
      characterWeight d p (determinant g) * detNormPower s g := by
    rw [weight_add, mul_assoc, ← power_add, show 1 / 2 + (s - 1 / 2) = s by ring]
  calc
    _ = c * ∫ h, I h ∂ν := by
      simp only [I, integral_mul_const, integral_const_mul, F]
      ring
    _ = c * ∫ h, I (h * g⁻¹) ∂ν := by rw [integral_mul_right_eq_self]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with h
      have hg : (h * g⁻¹) * g = h := by rw [mul_assoc, inv_mul_cancel, mul_one]
      have hd : characterWeight d p (determinant (h * g⁻¹)) *
          characterWeight d p (determinant g) = characterWeight d p (determinant h) := by
        rw [← map_mul, ← map_mul, hg]
      simp only [I, F, hg, mul_inv_rev, inv_inv, intermediateRaw]
      calc
        _ = (characterWeight d (p + 1 / 2) (determinant g) * detNormPower (s - 1 / 2) g) *
            (Φ h.val * φ (Langlands.RankinSelberg.lastRow (g * h⁻¹)) * W (g * h⁻¹) *
              characterWeight d p (determinant (h * g⁻¹)) * V g) := by ring
        _ = _ := by
          rw [hdet]
          linear_combination
            (Φ h.val * W (g * h⁻¹) * V g * φ (Langlands.RankinSelberg.lastRow (g * h⁻¹)) *
              detNormPower s g) * hd

/-- The two changes of variables in (8.3), from the adjacent Godement formula to the
unfolded integral. Absolute integrability of the unfolded product legitimizes Fubini. -/
def ComplexAdjacentUnfoldingStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData r) [SFinite D.measure]
    (ν : Measure G) [SFinite ν] [ν.IsMulRightInvariant]
    (d : ComplexCharacterData) (p s : ℂ) (Φ : Mat → ℂ) (φ : Vec → ℂ) (a : ℂˣ)
    (W V : G → ℂ) (Wbig : G' → ℂ) (c : ℂ),
    (∀ (u : N) g, W (u.val * g) = complexWhittakerCharacter a u.val * W g) →
    (∀ (u : N) g, V (u.val * g) = complexWhittakerCharacter (-a) u.val * V g) →
    (∀ g, Wbig (padGL (Nat.le_succ r.succ) g) = c *
      characterWeight d (p + 1 / 2) (determinant g) *
        ∫ h, Φ (h * g).val * φ (Langlands.RankinSelberg.lastRow h⁻¹) * W h⁻¹ * characterWeight d p (determinant h) ∂ν) →
    Integrable (unfoldedKernel d p s Φ φ W V) (ν.prod D.measure) →
    complexUnequalIntegral (Nat.lt_succ_self r) D Wbig V s =
      c * ∫ x, unfoldedKernel d p s Φ φ W V x ∂ν.prod D.measure

theorem complexAdjacentUnfolding : ComplexAdjacentUnfoldingStatement (r := r) := by
  intro D _ ν _ _ d p s Φ φ a W V Wbig c hW hV hBig hU
  let I := intermediateKernel d p s Φ φ W V
  let U := unfoldedKernel d p s Φ φ W V
  have hcomp : I ∘ rightShear N = U := unfolded_eq_comp_shear d p s Φ φ W V hW hV
  have : SecondCountableTopology Q := (leftQuotient_isOpenQuotientMap N).secondCountableTopology
  let := D.unipotentHaar_rightInvariant
  have hpres := quotientRightShear_measurePreserving N ν D.measure D.compatible.right_invariant
  let e := (rightShear N).toMeasurableEquiv
  have hI : Integrable I (ν.prod D.measure) :=
    (hpres.integrable_comp_emb e.measurableEmbedding).mp (hcomp.symm ▸ hU)
  have hIavg (q : Q) : complexUnequalIntegrand (Nat.lt_succ_self r) Wbig V s q =
      c * ∫ h, I (h, q) ∂ν := by
    change Wbig (padGL (Nat.le_succ r.succ) q.out) * V q.out *
      ArchimedeanLocal.detPower complexNormalizedAbs q.out (s - (((r.succ - r : ℕ) : ℂ)) / 2) = _
    rw [show r.succ - r = 1 by omega, Nat.cast_one, detPower_eq, hBig]
    exact unfold_inner ν d p s Φ φ W V q.out c
  change (∫ q, complexUnequalIntegrand (Nat.lt_succ_self r) Wbig V s q ∂D.measure) = _
  simp_rw [hIavg, integral_const_mul]
  congr 1
  calc
    (∫ q, ∫ h, I (h, q) ∂ν ∂D.measure) = ∫ x, I x ∂ν.prod D.measure :=
      (integral_prod_symm I hI).symm
    _ = ∫ x, I (e x) ∂ν.prod D.measure := (hpres.integral_comp' I).symm
    _ = _ := by change (∫ x, (I ∘ rightShear N) x ∂ν.prod D.measure) = _; rw [hcomp]

end Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding
