import Langlands.Global.RankinSelberg.UnequalFactorizationAtStatement
import Langlands.Global.RankinSelberg.UnipotentClassProductProof
import Langlands.Global.RankinSelberg.RectangleTateProof

/-! # Proof of the fieldwise unequal-rank integration step

At a fixed number field `F`, pointwise unequal-rank factorization on the partial integral
classes implies the integrated factorization. The argument replays
`unequalArchimedeanFactorizationReduction` with the pointwise premise used only at `F`, and
with the published quotient-product and rectangular Tate identities.
-/

noncomputable section
universe u uQ
open NumberField MeasureTheory
open Langlands.Global.HeckeFunctionalEquation Langlands.Global.CuspidalPairFunctionalEquation
open Langlands.LocalFactor.Archimedean
open Langlands.Global.CompletionPadic Langlands.ClassFieldTheory.Global.RelativeWeilGroup
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance unequalFactorizationAtProofSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance unequalFactorizationAtProofSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

attribute [local instance] rectangleMeasurableSpace rectangleBorelSpace
attribute [local instance] ArchimedeanLocal.archimedeanRealQMeasurable
  ArchimedeanLocal.archimedeanRealQBorel ArchimedeanLocal.archimedeanComplexQMeasurable
  ArchimedeanLocal.archimedeanComplexQBorel ArchimedeanLocal.archimedeanRealGLMeasurable
  ArchimedeanLocal.archimedeanRealGLBorel ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel ArchimedeanLocal.archimedeanRealNMeasurable
  ArchimedeanLocal.archimedeanRealNBorel ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel

open RankinSelberg (LeftUnipotentQuotient rectangularMeasure)

/-- Fieldwise integration: at each number field `F`, `UnequalPointwiseFactorizationAt F`
implies `UnequalArchimedeanFactorizationAt F`. The pointwise identities are integrated over
`unipotentIntegralClasses F (t+1) S` with the quotient-product identity, after the
rectangular dual integral is evaluated with the rectangular Tate identity. The constant is
`c = C κ` and the half-plane bound is `σ = 0`. -/
theorem unequalArchimedeanFactorizationAtReduction :
    UnequalArchimedeanFactorizationAtReductionStatement.{u, uQ} := by
  classical
  intro F _ _ _ hA ψ hψ r t h T Td T' Td' hTd hTd' P P' hI hI' S hPS hP'S hsupp aR haR aC haC
    dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd' ψv hψv νv hνv
  have hB := UnipotentClass.unipotentClassProductStatement.{u}
  have hC := RectangleTate.rectangleTateStatement.{u}
  obtain ⟨x, x', hx, hx', κ, WR, WR', DR, WC, WC', DC, D, fS, gS, hκ, hWR, hWR', hWC, hWC',
      hfS, hgS, hord, hdual, hn1, hn2, hn3, hn4⟩ :=
    hA ψ hψ r t h T Td T' Td' hTd hTd' P P' hI hI' S hPS hP'S hsupp aR haR aC haC
      dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd' ψv hψv νv hνv
  obtain ⟨CB, hCB, hprod⟩ := hB F t S DR DC (fun v => (D v).quotientMeasure)
    (fun v => (D v).isCompatible_quotientMeasure)
  refine ⟨x, x', hx, hx', CB * κ, WR, WR', DR, WC, WC', DC, 0, D, mul_ne_zero hCB hκ,
    hWR, hWR', hWC, hWC', ?_, ?_, hn1, hn2, hn3, hn4⟩
  · intro s _
    rw [partialUnequalWhittakerIntegral_eq_setIntegral,
      setIntegral_congr_fun (measurableSet_unipotentIntegralClasses (t + 1) S)
        (fun q hq => hord s q hq),
      integral_const_mul, hprod]
    rw [Finset.prod_congr rfl (fun v _ => hfS v s)]
    simp only [ArchimedeanLocal.realUnequalIntegral, ArchimedeanLocal.complexUnequalIntegral,
      ArchimedeanLocal.unequalIntegral, ArchimedeanLocal.realUnequalIntegrand,
      ArchimedeanLocal.complexUnequalIntegrand]
    ring
  · intro s _
    have key : ∀ q ∈ unipotentIntegralClasses F (t + 1) S,
        dualWhittakerIntegrand F h
            (translateFunction F (r + 1) (unfoldingWeyl F h)
              (dualFunction F (r + 1) (cuspWhittaker F T ψ.complex x)))
            (dualFunction F (t + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')) s q =
          κ * ((∏ v, ∫ y, ArchimedeanLocal.realUnequalDualKernel h (WR v) (WR' v) s
                (realQuotientProjection F t v q, y)
                ∂rectangularMeasure (ArchimedeanLocal.realSelfDualMeasure (aR v))
                  (r - (t + 1)) (t + 1)) *
            (∏ w, ∫ y, ArchimedeanLocal.complexUnequalDualKernel h (WC w) (WC' w) s
                (complexQuotientProjection F t w q, y)
                ∂rectangularMeasure (ArchimedeanLocal.complexSelfDualMeasure (aC w))
                  (r - (t + 1)) (t + 1)) *
            ∏ v : S, padicRectIntegral (padicField v.1) (r - (t + 1)) (t + 1) (νv v.1)
              (fun y => gS v s (finiteQuotientProjection F t v.1 q, y))) := by
      intro q hq
      unfold dualWhittakerIntegrand
      rw [integral_congr_ae (Filter.Eventually.of_forall (hdual s q hq)), integral_const_mul]
      exact congrArg (κ * ·) (hC F ψ hψ S hsupp aR haR aC haC ψv hψv νv hνv
        (r - (t + 1)) (t + 1)
        (fun v y => ArchimedeanLocal.realUnequalDualKernel h (WR v) (WR' v) s
          (realQuotientProjection F t v q, y))
        (fun w y => ArchimedeanLocal.complexUnequalDualKernel h (WC w) (WC' w) s
          (complexQuotientProjection F t w q, y))
        (fun v y => gS v s (finiteQuotientProjection F t v.1 q, y)))
    have hgS' : ∀ v : S, padicQuotientIntegral (padicField v.1) (D v).quotientMeasure
        (fun p => padicRectIntegral (padicField v.1) (r - (t + 1)) (t + 1) (νv v.1)
          (fun y => gS v s (p, y))) = (D v).dualIntegral h (νv v.1) s :=
      fun v => hgS v s
    rw [partialDualWhittakerIntegral_eq_setIntegral,
      setIntegral_congr_fun (measurableSet_unipotentIntegralClasses (t + 1) S) key,
      integral_const_mul,
      hprod (fun v p => ∫ y, ArchimedeanLocal.realUnequalDualKernel h (WR v) (WR' v) s (p, y)
          ∂rectangularMeasure (ArchimedeanLocal.realSelfDualMeasure (aR v))
            (r - (t + 1)) (t + 1))
        (fun w p => ∫ y, ArchimedeanLocal.complexUnequalDualKernel h (WC w) (WC' w) s (p, y)
          ∂rectangularMeasure (ArchimedeanLocal.complexSelfDualMeasure (aC w))
            (r - (t + 1)) (t + 1))
        (fun v p => padicRectIntegral (padicField v.1) (r - (t + 1)) (t + 1) (νv v.1)
          (fun y => gS v s (p, y))),
      Finset.prod_congr rfl (fun v _ => hgS' v)]
    simp only [ArchimedeanLocal.realUnequalDualIntegral,
      ArchimedeanLocal.complexUnequalDualIntegral, ArchimedeanLocal.blockIntegral,
      ArchimedeanLocal.realUnequalDualKernel, ArchimedeanLocal.complexUnequalDualKernel]
    ring

end Langlands.Global.RankinSelbergGlobal
