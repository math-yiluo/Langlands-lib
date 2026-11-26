import Langlands.Global.RankinSelberg.EqualFactorizationAtStatement
import Langlands.Global.RankinSelberg.UnipotentClassProductProof

/-! # Same-field equal-rank Whittaker integration

The theorem `equalArchimedeanFactorizationAtReduction` proves
`EqualArchimedeanFactorizationAtReductionStatement`: at one number field `F`, the pointwise
equal-rank factorization `EqualPointwiseFactorizationAt F` implies the integrated
factorization `EqualArchimedeanFactorizationAt F`. Both pointwise identities are integrated
over `unipotentIntegralClasses F (r + 1) S` with the single quotient-product formula of
`UnipotentClass.unipotentClassProductStatement` at `F`. See the paired Markdown.
-/

noncomputable section
universe u uQ
open NumberField MeasureTheory
open Langlands.Global.HeckeFunctionalEquation Langlands.Global.CuspidalPairFunctionalEquation
open Langlands.LocalFactor.Archimedean
open Langlands.Global.CompletionPadic Langlands.ClassFieldTheory.Global.RelativeWeilGroup
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance equalAtIntegrationSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance equalAtIntegrationSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
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

open RankinSelberg (LeftUnipotentQuotient)

/-- Integrating the ordinary and dual pointwise identities at `F` over the integral quotient
classes, with one quotient-product constant, gives both integral identities at `F` with the
same nonzero scalar. -/
theorem equalArchimedeanFactorizationAtReduction :
    EqualArchimedeanFactorizationAtReductionStatement.{u, uQ} := by
  classical
  intro F _ _ _ hA ψ hψ r T Td T' Td' hTd hTd' P P' hI hI' S hPS hP'S hsupp aR haR aC haC
    dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd' ψv hψv νv hνv
  obtain ⟨x, x', Φ, hx, hx', hΦ, hΦS, κ, WR, WR', ΦR, DR, WC, WC', ΦC, DC, D, fS, gS,
      hκ, hWR, hWR', hWC, hWC', hΦprod, hΦhatprod, hfS, hgS, hord, hdual,
      hn1, hn2, hn3, hn4⟩ :=
    hA ψ hψ r T Td T' Td' hTd hTd' P P' hI hI' S hPS hP'S hsupp aR haR aC haC
      dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd' ψv hψv νv hνv
  obtain ⟨CB, hCB, hprod⟩ := UnipotentClass.unipotentClassProductStatement F r S DR DC
    (fun v => equalPadicQuotientMeasure (padicField v.1) r)
    (fun v => equalPadicQuotientMeasure_isCompatible (padicField v.1) r)
  refine ⟨x, x', Φ, hx, hx', hΦ, hΦS, CB * κ, WR, WR', ΦR, DR, WC, WC', ΦC, DC, 0, D,
    mul_ne_zero hCB hκ, hWR, hWR', hWC, hWC', hΦprod, hΦhatprod,
    ?_, ?_, hn1, hn2, hn3, hn4⟩
  · intro s _
    rw [partialEqualWhittakerIntegral_eq_setIntegral,
      setIntegral_congr_fun (measurableSet_unipotentIntegralClasses (r + 1) S)
        (fun q hq => hord s q hq),
      integral_const_mul, hprod]
    rw [Finset.prod_congr rfl (fun v _ => hfS v s)]
    simp only [ArchimedeanLocal.realEqualIntegral, ArchimedeanLocal.complexEqualIntegral,
      ArchimedeanLocal.equalIntegral, ArchimedeanLocal.realEqualIntegrand,
      ArchimedeanLocal.complexEqualIntegrand]
    ring
  · intro s _
    rw [partialEqualWhittakerIntegral_eq_setIntegral,
      setIntegral_congr_fun (measurableSet_unipotentIntegralClasses (r + 1) S)
        (fun q hq => hdual s q hq),
      integral_const_mul, hprod]
    rw [Finset.prod_congr rfl (fun v _ => hgS v s)]
    simp only [ArchimedeanLocal.realEqualDualIntegral,
      ArchimedeanLocal.complexEqualDualIntegral, ArchimedeanLocal.equalIntegral,
      ArchimedeanLocal.realEqualIntegrand, ArchimedeanLocal.complexEqualIntegrand]
    ring

end Langlands.Global.RankinSelbergGlobal
