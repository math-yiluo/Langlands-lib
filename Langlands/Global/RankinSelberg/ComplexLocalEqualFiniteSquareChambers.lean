import Langlands.Analysis.LandauMellin
import Langlands.Global.RankinSelberg.ComplexLocalEqualChamberTrace
import Langlands.Global.RankinSelberg.ComplexLocalEqualNormalizedFactors

/-! # The finite normalized trace on the common convergence chambers -/

noncomputable section

open Filter MeasureTheory
open Langlands.Archimedean Langlands.Automorphic Langlands.GeneralLinear Langlands.GodementJacquet
open Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Elementwise SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal
open ComplexGodement (shiftedCharacter shiftedCharacter_exponent)
open ComplexLocalWhittakerDual (dualData dualFunction_mem)
open Langlands.LandauMellin (eqOn_halfPlane isOpen_halfPlane)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}
local notation "m" => r + 1
local notation "n" => (r + 1) + 1
local notation "H" => Langlands.GeneralLinear m ℂ
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "Kc" => unitaryCompact ℂ n
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "Test" => 𝓢(Mat, ℂ)
local notation "gap" => Nat.lt_succ_self r
local notation "ud" => ArchimedeanLocal.dualFunction m
local notation "wd" => ArchimedeanLocal.dualFunction n

/-- A deep trace identity for a jointly entire function holds on the whole product
of right half-planes on which the test kernel is absolutely integrable. -/
theorem eq_normalized_unfolded_of_deep_chamber
    (D₁ : ComplexQuotientMeasureData r) [SFinite D₁.measure] (μ : Measure G) [SFinite μ]
    (d : ComplexCharacterData) (Φ : Test) (U : H → ℂ) (V : G → ℂ)
    {F N : ℂ × ℂ → ℂ} (hF : Differentiable ℂ F) (hN : Differentiable ℂ N)
    {τ σ : ℝ}
    (hInt : ∀ z s : ℂ, τ < z.re → σ < s.re →
      Integrable (complexEqualUnfoldedKernel (shiftedCharacter d z) Φ U V s) (D₁.measure.prod μ))
    (hDeep : ∃ τ' σ' : ℝ, ∀ z s : ℂ, τ' < z.re → σ' < s.re →
      F (z, s) = N (z, s) *
        complexEqualUnfoldedIntegral μ D₁ (shiftedCharacter d z).character.toMonoidHom Φ U V s) :
    ∀ z s : ℂ, τ < z.re → σ < s.re →
      F (z, s) = N (z, s) *
        complexEqualUnfoldedIntegral μ D₁ (shiftedCharacter d z).character.toMonoidHom Φ U V s := by
  obtain ⟨τ', σ', hDeep⟩ := hDeep
  let I (z s : ℂ) := complexEqualUnfoldedIntegral μ D₁
    (shiftedCharacter d z).character.toMonoidHom Φ U V s
  have hzI (s : ℂ) (hs : σ < s.re) :
      DifferentiableOn ℂ (fun z => I z s) {z : ℂ | τ < z.re} := by
    simpa only [I, coe_complexMatrixEntryToOperator, Complex.ofReal_one, Complex.ofReal_zero,
      one_mul, zero_mul, zero_add, add_zero] using
      differentiableOn_complexEqualUnfoldedIntegral_affine D₁ μ d (complexMatrixEntryToOperator Φ) U V 0 s 1 0
        (isOpen_halfPlane τ) (fun z hz => by simpa [coe_complexMatrixEntryToOperator] using hInt z s hz hs)
  have hsI (z : ℂ) (hz : τ < z.re) :
      DifferentiableOn ℂ (fun s => I z s) {s : ℂ | σ < s.re} := by
    simpa only [I, coe_complexMatrixEntryToOperator, Complex.ofReal_one, Complex.ofReal_zero,
      one_mul, zero_mul, zero_add, add_zero] using
      differentiableOn_complexEqualUnfoldedIntegral_affine D₁ μ d (complexMatrixEntryToOperator Φ) U V z 0 0 1
        (isOpen_halfPlane σ) (fun s hs => by simpa [coe_complexMatrixEntryToOperator] using hInt z s hz hs)
  have hZ (s : ℂ) (hs : max σ σ' < s.re) :
      Set.EqOn (fun z => F (z, s)) (fun z => N (z, s) * I z s) {z : ℂ | τ < z.re} :=
    eqOn_halfPlane (hF.comp (differentiable_id.prodMk (differentiable_const s))).differentiableOn
      ((hN.comp (differentiable_id.prodMk (differentiable_const s))).differentiableOn.mul
        (hzI s ((le_max_left _ _).trans_lt hs)))
      (fun z hz => hDeep z s hz ((le_max_right _ _).trans_lt hs))
  intro z s hz hs
  exact eqOn_halfPlane (hF.comp ((differentiable_const z).prodMk differentiable_id)).differentiableOn
    ((hN.comp ((differentiable_const z).prodMk differentiable_id)).differentiableOn.mul (hsI z hz))
    (fun t ht => hZ t ht hz) hs

private theorem differentiable_equalDoubleDenominator
    (d : ComplexCharacterData) (ds es : List ComplexCharacterData) :
    Differentiable ℂ (fun p : ℂ × ℂ => equalDoubleDenominator d ds es p.1 p.2) :=
  ((complexPairLFactor es ds).entire.comp differentiable_snd).mul
    ((complexPairLFactor [d] es).entire.comp (differentiable_snd.add differentiable_fst))

/-- The finite square-test producer in the two common chambers. The absolute
convergence thresholds can be chosen before the finite test. -/
def ComplexLocalEqualFiniteSquareChambersStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData (r + 1)) (D₁ : ComplexQuotientMeasureData r)
    (d : ComplexCharacterData) (ds : List ComplexCharacterData), ds.length = m →
  ∀ (e : Fin n → ComplexCharacterData) (U : complexWhittakerModel r ds 1)
    (B : complexStandardKFinite n (List.ofFn e) →ₗ[ℂ] (G → ℂ)),
    IsComplexWhittakerIntertwiner (r + 1) (List.ofFn e) (-1) B →
  ∀ (f : complexStandardKFinite n (List.ofFn e)),
    (∀ V : complexWhittakerModel (r + 1) (List.ofFn e) (-1),
      HasComplexPairNormalizedGrowth (List.ofFn e) ds (-1) (complexCentralSign ds ^ m)
        (complexUnequalIntegral gap D₁ V.val U.val)
        (complexUnequalDualIntegral gap (-1) D₁ V.val U.val)) →
    ∃ τ σ τd σd : ℝ,
      (∀ (Φ : Test) (z s : ℂ), τ < z.re → σ < s.re →
        Integrable (complexEqualUnfoldedKernel (shiftedCharacter d z) Φ U.val (B f) s)
          (D₁.measure.prod D.groupHaar)) ∧
      (∀ (Φ : Test) (z s : ℂ), τd < (-z).re → σd < s.re →
        Integrable (complexEqualUnfoldedKernel (shiftedCharacter d.inv (-z)) Φ (ud U.val) (wd (B f)) s)
          (D₁.measure.prod D.groupHaar)) ∧
      ∀ Ψ Ψd : Test, (Ψd : Mat → ℂ) = complexMatrixFourier 1 Ψ →
        FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : Kc => fun X => Ψ ((k.val⁻¹).val * X))) →
        ∃ F : ℂ × ℂ → ℂ, Differentiable ℂ F ∧
          (∀ z : ℂ, HasStripExponentialGrowth (fun s => F (z, s))) ∧
          (∀ v : ℂ, HasStripExponentialGrowth (fun s => F (v + s, s))) ∧
          (∀ z s : ℂ, τ < z.re → σ < s.re →
            F (z, s) = equalDoubleDenominator d ds (List.ofFn e) z s *
              complexEqualUnfoldedIntegral D.groupHaar D₁
                (shiftedCharacter d z).character.toMonoidHom Ψ U.val (B f) s) ∧
          (∀ z s : ℂ, τd < (-z).re → σd < s.re →
            F (z, 1 - s) = (equalDoublePhase d ds (List.ofFn e))⁻¹ *
              (equalDoubleDualDenominator d ds (List.ofFn e) z s *
                complexEqualUnfoldedIntegral D.groupHaar D₁
                  (shiftedCharacter d.inv (-z)).character.toMonoidHom Ψd (ud U.val) (wd (B f)) s))

set_option maxHeartbeats 1200000 in
theorem complexLocalEqualFiniteSquareChambers :
    ComplexLocalEqualFiniteSquareChambersStatement (r := r) := by
  intro D D₁ d ds hds e U B hB f hAdj
  let es := List.ofFn e
  have hes : es.length = n := List.length_ofFn
  let V : complexWhittakerModel (r + 1) es (-1) :=
    ⟨B f, Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨f, rfl⟩)⟩
  let Ud : complexWhittakerModel r (dualData ds) (-1) := ⟨ud U.val, dualFunction_mem hds U.2⟩
  let Vd : complexWhittakerModel (r + 1) (dualData es) (-(-1 : ℂˣ)) :=
    ⟨wd V.val, dualFunction_mem hes V.2⟩
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let : SigmaFinite D.groupHaar := complexLocalGroupHaarSigmaFinite D
  let : SigmaFinite D₁.measure := complexLocalQuotientSigmaFinite D₁
  obtain ⟨T, σ, hI⟩ := complexLocalEqualProductTrace D₁ D.groupHaar 1 ds es U V
  obtain ⟨Td, σd, hId⟩ :=
    complexLocalEqualProductTrace D₁ D.groupHaar (-1) (dualData ds) (dualData es) Ud Vd
  let τ := T - d.exponent.re
  let τd := Td - d.inv.exponent.re
  have hPos (Φ : Test) (z s : ℂ) (hz : τ < z.re) (hs : σ < s.re) :
      Integrable (complexEqualUnfoldedKernel (shiftedCharacter d z) Φ U.val V.val s)
        (D₁.measure.prod D.groupHaar) := by
    have hx : T ≤ (shiftedCharacter d z).exponent.re := by
      rw [shiftedCharacter_exponent, Complex.add_re]
      dsimp only [τ] at hz
      linarith
    obtain ⟨_, _, _, h⟩ := hI (shiftedCharacter d z) s hx hs
    simpa only [coe_complexMatrixEntryToOperator] using (h (complexMatrixEntryToOperator Φ) _ _ rfl rfl).1
  have hNeg (Φ : Test) (z s : ℂ) (hz : τd < z.re) (hs : σd < s.re) :
      Integrable (complexEqualUnfoldedKernel (shiftedCharacter d.inv z) Φ Ud.val Vd.val s)
        (D₁.measure.prod D.groupHaar) := by
    have hx : Td ≤ (shiftedCharacter d.inv z).exponent.re := by
      rw [shiftedCharacter_exponent, Complex.add_re]
      dsimp only [τd] at hz
      linarith
    obtain ⟨_, _, _, h⟩ := hId (shiftedCharacter d.inv z) s hx hs
    simpa only [coe_complexMatrixEntryToOperator] using (h (complexMatrixEntryToOperator Φ) _ _ rfl rfl).1
  refine ⟨τ, σ, τd, σd, hPos, fun Φ z => hNeg Φ (-z), fun Ψ Ψd hFourier hFinite => ?_⟩
  obtain ⟨F, hF, hStrip, hTilt, hDeep, hDeepd⟩ :=
    complexLocalEqualFiniteSquareNormalized D D₁ d ds hds e U B hB f Ψ Ψd hFourier hFinite hAdj
  refine ⟨F, hF, hStrip, hTilt, ?_, ?_⟩
  · exact eq_normalized_unfolded_of_deep_chamber D₁ D.groupHaar d Ψ U.val V.val hF
      (differentiable_equalDoubleDenominator d ds es) (hPos Ψ) hDeep
  · let Gd (p : ℂ × ℂ) := F (-p.1, 1 - p.2)
    let Nd (p : ℂ × ℂ) := (equalDoublePhase d ds es)⁻¹ *
      equalDoubleDenominator d.inv (ds.map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv) p.1 p.2
    have hGd : Differentiable ℂ Gd := hF.comp
      (differentiable_fst.neg.prodMk ((differentiable_const _).sub differentiable_snd))
    have hNd : Differentiable ℂ Nd := (differentiable_equalDoubleDenominator _ _ _).const_mul _
    have hDeep' : ∃ τ' σ' : ℝ, ∀ z s : ℂ, τ' < z.re → σ' < s.re →
        Gd (z, s) = Nd (z, s) *
          complexEqualUnfoldedIntegral D.groupHaar D₁ (shiftedCharacter d.inv z).character.toMonoidHom
            Ψd Ud.val Vd.val s := by
      obtain ⟨τ', σ', h⟩ := hDeepd
      refine ⟨τ', σ', fun z s hz hs => ?_⟩
      simpa only [Gd, Nd, equalDoubleDualDenominator, neg_neg, mul_assoc] using
        h (-z) s (by simpa only [neg_neg] using hz) hs
    intro z s hz hs
    have h := eq_normalized_unfolded_of_deep_chamber D₁ D.groupHaar d.inv Ψd Ud.val Vd.val hGd hNd
      (hNeg Ψd) hDeep' (-z) s hz hs
    simpa only [Gd, Nd, equalDoubleDualDenominator, neg_neg, mul_assoc] using h

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
