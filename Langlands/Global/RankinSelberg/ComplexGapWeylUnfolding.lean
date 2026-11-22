import Langlands.Global.RankinSelberg.ComplexGapSplitPartialRestriction
import Langlands.Global.RankinSelberg.ComplexGapWeylTranslation
import Langlands.Global.RankinSelberg.ComplexLocalUnequalKernels
import Langlands.Global.RankinSelberg.DualExpansionData
import Langlands.Representation.RankinSelberg.AdjacentRankQuotientShear

/-! # The quotient substitution in the alternate complex integral -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped Matrix.Norms.Elementwise SchwartzMap NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapWeylUnfolding

open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open Langlands.GeneralLinear (determinant rankInclusion)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.QuotientIntegration (rightTranslate continuous_rightTranslate_joint descend)
open Langlands.RankinSelberg (LeftUnipotentQuotient det_rankInclusion unipotent_det)
open ArchimedeanLocal (ComplexQuotientMeasureData complexNormalizedAbs complexSelfDualMeasure
  complexUnequalIntegral)
open ComplexGapSplitPartialRestriction (HasSplitPartialTest complexGapSplitPartialRestriction)
open ComplexGapTailExchange (SplitTailTest alternateBlockTailKernel fixedTailFactor)
open ComplexGapTriangularChart (Outer retainedMatrix outerMeasure)
open ComplexGapUpperTail (packedTail)
open ComplexGapWeylTranslation (continuedValue_mul_weyl)
open ComplexGodement (characterWeight)
open ComplexGodementAddedCharacter (continuedValue rightTest)
open ComplexJacquetUnipotentMeasure (entryHaar entryHaar_sigmaFinite)

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel ArchimedeanLocal.archimedeanComplexQMeasurable
  ArchimedeanLocal.archimedeanComplexQBorel ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel

/-- Padding by a fixed additional rank is the standard rank inclusion. -/
theorem padGL_eq_rankInclusion {m n : ℕ} (g : G m) :
    padGL (Nat.le_add_right m n) g = rankInclusion n g := by
  ext i j
  refine Fin.addCases (m := m) (n := n) (fun i₀ => ?_) (fun i₁ => ?_) i <;>
    refine Fin.addCases (m := m) (n := n) (fun j₀ => ?_) (fun j₁ => ?_) j <;>
    (simp [UnequalAnalytic.padGL_apply, rankInclusion, Matrix.one_apply, Fin.ext_iff]; try omega)

private theorem detPower_mul {n : ℕ} (g h : G n) (s : ℂ) : P (g * h) s = P g s * P h s := by
  have hp (x : G n) : ‖x.val.det‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr x.det_ne_zero)
  simp only [ArchimedeanLocal.detPower, complexNormalizedAbs, Units.val_mul, Matrix.det_mul,
    norm_mul, mul_pow, Real.log_mul (hp g) (hp h), Complex.ofReal_add, mul_add, Complex.exp_add]

private theorem detPower_add {n : ℕ} (g : G n) (s u : ℂ) : P g (s + u) = P g s * P g u := by
  simp only [ArchimedeanLocal.detPower, add_mul, Complex.exp_add]

variable (t q : ℕ)

local notation "Small" => (t + 1)
local notation "Order" => (t + 1 + q)
local notation "Size" => (t + 1 + q + 1)
local notation "Compact" => unitaryCompact ℂ (t + 1 + q + 1)
local notation "Q" => LeftUnipotentQuotient t ℂ
local notation "U" => Langlands.GeneralLinear.upperUnipotent (t + 1) ℂ
local notation "N" => Langlands.GeneralLinear.upperUnipotent (q + 1) ℂ
local notation "Tails" => (Outer (t + 1) q × N)
local notation "Rect" => Matrix (Fin (t + 1 + q + 1)) (Fin (t + 1 + q + 2)) ℂ
local notation "embed" => (rankInclusion (q + 1) : G Small →* G Size)

private theorem lt_order : t < Order := by omega

private theorem lt_order_succ : t < Order + 1 := by omega

/-- The retained chart matrix with the unipotent tail inserted. -/
def tailMatrix (p : Tails) : G Size :=
  retainedMatrix Small q p.1 * (packedTail Small q 0 p.2).val

/-- The determinant factor from the partial Fourier exchange in the tail rectangles. -/
def tailJacobian (p : Tails) : ℂ :=
  (((complexNormalizedAbs (retainedMatrix Small q p.1).val.det)⁻¹ : ℝ) : ℂ) ^ q

private def leadingMatrix (p : Tails) : G Small := p.1.1.1.1

private def beforeShear (a : ℂˣ) (T : SplitTailTest Small q) (χ : ℂˣ →* ℂ)
    (W : G Size → ℂ) (V : G Small → ℂ) (u : ℂ) (p : Tails × Q) : ℂ :=
  let g := p.2.out
  tailJacobian t q p.1 *
    alternateBlockTailKernel Small q a T W χ g (leadingMatrix t q p.1)
      (retainedMatrix Small q p.1.1) p.1.2 * (V g * P g u)

/-- The alternate kernel after substituting `g h` for `g`, with the leading matrix `h`
now translating only the smaller Whittaker argument. -/
def weylUnfoldedKernel (a : ℂˣ) (T : SplitTailTest Small q) (χ : ℂˣ →* ℂ)
    (W : G Size → ℂ) (V : G Small → ℂ) (u : ℂ) (p : Tails × Q) : ℂ :=
  let g := p.2.out
  let h := leadingMatrix t q p.1
  let B := tailMatrix t q p.1
  (tailJacobian t q p.1 * alternateBlockTailKernel Small q a T (fun _ => 1) χ 1 h
    (retainedMatrix Small q p.1.1) p.1.2 * P h u) *
      (W (embed g * B⁻¹) * V (g * h) * P g u)

private def inverseShear (p : Tails × Q) : Tails × Q :=
  (p.1, rightTranslate U (leadingMatrix t q p.1)⁻¹ p.2)

set_option maxHeartbeats 950000 in
private theorem inverseShear_preserving (D : ComplexQuotientMeasureData t)
    (η : Measure Tails) [SFinite η] [SFinite D.measure] :
    MeasurePreserving (inverseShear t q) (η.prod D.measure) (η.prod D.measure) := by
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  refine (MeasurePreserving.id η).skew_product
    (g := fun p x => rightTranslate U (leadingMatrix t q p)⁻¹ x) ?_ ?_
  · let pair (p : Tails × Q) : Q × G Small := (p.2, (leadingMatrix t q p.1)⁻¹)
    let translate (p : Q × G Small) : Q := rightTranslate U p.2 p.1
    have hLead : Continuous (fun p : Tails × Q => leadingMatrix t q p.1) := by
      unfold leadingMatrix
      fun_prop
    have hPair : Measurable pair := measurable_snd.prodMk hLead.inv.measurable
    have hTranslate : Measurable translate := (continuous_rightTranslate_joint U).measurable
    change Measurable (translate ∘ pair)
    exact hTranslate.comp hPair
  · exact ae_of_all _ fun p => (D.compatible.right_invariant (leadingMatrix t q p)⁻¹).map_eq

set_option maxHeartbeats 950000 in
/-- The sheared kernel may be evaluated at any representative of the smaller quotient. -/
theorem weylUnfoldedKernel_mk (a : ℂˣ) (ds es : List ComplexCharacterData)
    (W : complexWhittakerModel Order ds (-a)) (V : complexWhittakerModel t es a)
    (T : SplitTailTest Small q) (χ : ℂˣ →* ℂ) (u : ℂ) (p : Tails) (g : G Small) :
    weylUnfoldedKernel t q a T χ W.val V.val u (p, Quotient.mk _ g) =
      (tailJacobian t q p * alternateBlockTailKernel Small q a T (fun _ => 1) χ 1
        (leadingMatrix t q p) (retainedMatrix Small q p.1) p.2 * P (leadingMatrix t q p) u) *
        (W.val (embed g * (tailMatrix t q p)⁻¹) * V.val (g * leadingMatrix t q p) * P g u) := by
  let h := leadingMatrix t q p
  let B := tailMatrix t q p
  let f (x : G Small) := W.val (embed x * B⁻¹) * V.val (x * h) * P x u
  have hInv (u₀ : U) (x : G Small) : f (u₀.val * x) = f x := by
    unfold f
    have hProd := complexUnequalTranslatedProduct_unipotent_mul (lt_order t q) W.2
      (show V.val ∈ complexWhittakerModel t es (-(-a)) by simpa only [neg_neg] using V.2) u₀ x h B⁻¹
    have hPad (z : G Small) : padGL (Nat.succ_le_succ (lt_order t q).le) z = embed z :=
      padGL_eq_rankInclusion (m := Small) (n := q + 1) z
    simp_rw [hPad] at hProd
    rw [hProd]
    simp only [ArchimedeanLocal.detPower, Units.val_mul, Matrix.det_mul, unipotent_det, one_mul]
  have hRep := congrArg (descend U f hInv) (Quotient.out_eq (Quotient.mk (QuotientGroup.rightRel U) g))
  change f (Quotient.mk (QuotientGroup.rightRel U) g).out = f g at hRep
  unfold weylUnfoldedKernel
  exact congrArg (_ * ·) hRep

private theorem beforeShear_eq (a : ℂˣ) (ds es : List ComplexCharacterData)
    (W : complexWhittakerModel Order ds (-a)) (V : complexWhittakerModel t es a)
    (T : SplitTailTest Small q) (χ : ℂˣ →* ℂ) (u : ℂ) (p : Tails × Q) :
    beforeShear t q a T χ W.val V.val u p =
      weylUnfoldedKernel t q a T χ W.val V.val u (inverseShear t q p) := by
  let g := p.2.out
  let h := leadingMatrix t q p.1
  have hRep : (inverseShear t q p).2 = Quotient.mk _ (g * h⁻¹) := by
    change rightTranslate U h⁻¹ p.2 = _
    conv_lhs => rw [← Quotient.out_eq p.2]
    rfl
  rw [show inverseShear t q p = (p.1, Quotient.mk _ (g * h⁻¹)) from Prod.ext rfl hRep,
    weylUnfoldedKernel_mk t q a ds es W V T χ u]
  change tailJacobian t q p.1 * alternateBlockTailKernel Small q a T W.val χ g h
    (retainedMatrix Small q p.1.1) p.1.2 * (V.val g * P g u) =
    _ * (W.val (embed (g * h⁻¹) * (tailMatrix t q p.1)⁻¹) *
    V.val (g * h⁻¹ * h) * P (g * h⁻¹) u)
  have hPower : P g u = P (g * h⁻¹) u * P h u := by
    rw [← detPower_mul, inv_mul_cancel_right]
  rw [inv_mul_cancel_right g h, hPower]
  simp only [alternateBlockTailKernel, fixedTailFactor, tailMatrix]
  ring

/-- Jacquet's alternate restriction followed by the exact right Haar quotient substitution. -/
def ComplexGapWeylUnfoldingStatement : Prop :=
  ∀ (a : ℂˣ) (κ : Measure Compact), κ.IsHaarMeasure → κ.IsInvInvariant →
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (D : ComplexQuotientMeasureData t)
      (d : ComplexCharacterData) (ds es : List ComplexCharacterData)
      (Φ : 𝓢(Rect, ℂ)) (T : SplitTailTest Small q),
      let w := ArchimedeanLocal.unfoldingWeyl (K := ℂ) (lt_order_succ t q)
      HasSplitPartialTest Small q a (rightTest w Φ) T →
      ∀ (W : complexWhittakerModel Order ds (-a)) (V : complexWhittakerModel t es a) (z s : ℂ),
        let μ := complexSelfDualMeasure a
        let ν := complexGeneralLinearHaar Size
        let η := (outerMeasure Small q μ κ).prod (entryHaar μ (q + 1))
        let u := s - ((q + 1 : ℕ) : ℂ) / 2
        let χ := characterWeight d (((Order + 2 : ℕ) : ℂ) / 2 + z - 1)
        let F := weylUnfoldedKernel t q a T χ W.val V.val u
        Integrable F (η.prod D.measure) →
        complexUnequalIntegral (lt_order_succ t q) D
          (fun g => continuedValue ν μ d a Φ W.val (g * w) z) V.val s =
        ((d.character (determinant w) : ℂ) * (d.character ((-1 : ℂˣ) ^ Size) : ℂ)) *
          (c : ℂ) * ∫ p, ∫ x, F (p, x) ∂D.measure ∂η

set_option maxHeartbeats 950000 in
theorem complexGapWeylUnfolding : ComplexGapWeylUnfoldingStatement t q := by
  intro a κ hκ hκinv
  obtain ⟨c, hc, hRestriction⟩ := complexGapSplitPartialRestriction Small q (Nat.succ_pos t) a κ hκ hκinv
  refine ⟨c, hc, ?_⟩
  intro D d ds es Φ T w hΦ W V z s μ ν η u χ F hF
  let B := beforeShear t q a T χ W.val V.val u
  let C := (d.character (determinant w) : ℂ) * (d.character ((-1 : ℂˣ) ^ Size) : ℂ) * (c : ℂ)
  let θ := outerMeasure Small q μ κ
  let ρ := entryHaar μ (q + 1)
  let : κ.IsHaarMeasure := hκ
  let : CompactSpace Compact := Langlands.Archimedean.ComplexDuality.compactSpace_unitaryCompact _
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  let : SigmaFinite θ := by unfold θ outerMeasure; infer_instance
  let : SigmaFinite ρ := entryHaar_sigmaFinite μ _
  let : SFinite η := inferInstanceAs (SFinite (θ.prod ρ))
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : D.measure.Regular := D.compatible.regular
  let e := inverseShear t q
  have he : MeasurePreserving e (η.prod D.measure) (η.prod D.measure) :=
    inverseShear_preserving t q D η
  have hB : B = F ∘ e := funext (beforeShear_eq t q a ds es W V T χ u)
  have hFMap : Integrable F ((η.prod D.measure).map e) := he.map_eq.symm ▸ hF
  have hIntB : Integrable B (η.prod D.measure) := hB.symm ▸
    (integrable_map_measure hFMap.aestronglyMeasurable he.measurable.aemeasurable).mp hFMap
  have hShear : (∫ v, B v ∂η.prod D.measure) = ∫ v, F v ∂η.prod D.measure := by
    rw [hB]
    change (∫ v, F (e v) ∂η.prod D.measure) = _
    rw [← integral_map he.measurable.aemeasurable hFMap.aestronglyMeasurable, he.map_eq]
  have hPad (g : G Small) : padGL (Nat.succ_le_succ (lt_order_succ t q).le) g =
      padGL (Nat.le_succ Size) (embed g) := by
    calc
      _ = padGL (Nat.le_succ Size) (padGL (Nat.le_add_right Small (q + 1)) g) :=
        (Unfolding.padGL_comp (Nat.le_add_right Small (q + 1)) (Nat.le_succ Size) g).symm
      _ = _ := congrArg (padGL (Nat.le_succ Size)) (padGL_eq_rankInclusion (m := Small) (n := q + 1) g)
  have hP (g : G Small) : P (embed g) (1 / 2) = P g (1 / 2) := by
    simp only [ArchimedeanLocal.detPower, det_rankInclusion]
  have hU (g : G Small) :
      P g (1 / 2) * P g (s - (((Order + 1) - t : ℕ) : ℂ) / 2) = P g u := by
    rw [← detPower_add, show Order + 1 - t = q + 2 by omega]
    congr 1
    dsimp only [u]
    push_cast
    ring
  change _ = C * _
  calc
    _ = C * ∫ x : Q, ∫ p, ∫ Z, B ((p, Z), x) ∂ρ ∂θ ∂D.measure := by
      unfold complexUnequalIntegral ArchimedeanLocal.unequalIntegral ArchimedeanLocal.unequalIntegrand
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      let g := x.out
      change continuedValue ν μ d a Φ W.val
        (padGL (Nat.succ_le_succ (lt_order_succ t q).le) g * w) z *
        V.val g * P g (s - (((Order + 1) - t : ℕ) : ℂ) / 2) = _
      rw [hPad, continuedValue_mul_weyl (lt_order_succ t q),
        (hRestriction d ds (rightTest w Φ) T hΦ W g z).2, hP]
      have hInner (p : Outer Small q) :
          (∫ Z, B ((p, Z), x) ∂ρ) =
            (((complexNormalizedAbs (retainedMatrix Small q p).val.det)⁻¹ : ℝ) : ℂ) ^ q *
              (∫ Z, alternateBlockTailKernel Small q a T W.val χ g p.1.1.1
                (retainedMatrix Small q p) Z ∂ρ) * (V.val g * P g u) := by
        change (∫ Z, tailJacobian t q (p, Z) *
          alternateBlockTailKernel Small q a T W.val χ g p.1.1.1
            (retainedMatrix Small q p) Z * (V.val g * P g u) ∂ρ) = _
        simp only [tailJacobian]
        rw [integral_mul_const, integral_const_mul]
      simp_rw [hInner]
      rw [integral_mul_const, ← hU]
      dsimp only [C]
      ring
    _ = C * ∫ x : Q, ∫ p, B (p, x) ∂η ∂D.measure := by
      congr 1
      refine integral_congr_ae (hIntB.prod_left_ae.mono fun x hx => ?_)
      exact (integral_prod (fun p => B (p, x)) hx).symm
    _ = C * ∫ v, B v ∂η.prod D.measure := congrArg (C * ·) (integral_prod_symm B hIntB).symm
    _ = C * ∫ v, F v ∂η.prod D.measure := congrArg (C * ·) hShear
    _ = _ := congrArg (C * ·) (integral_prod F hF)

end Langlands.Global.RankinSelbergGlobal.ComplexGapWeylUnfolding
