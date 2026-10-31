import Langlands.Shimura.PEL.HarrisDeterminantCentralTrace
import Langlands.Shimura.PEL.RationalLieDeterminantCondition
import Langlands.AbelianScheme.LieRationalBaseIndependence

/-! # The normalized Harris–Taylor rational Lie determinant through one CM map -/

noncomputable section

open CategoryTheory _root_.AlgebraicGeometry
open Langlands.AbelianScheme
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField _root_.Algebra

variable {E F A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field F] [NumberField F] [IsTotallyComplex F]
    [Algebra E F] [IsQuadraticExtension E F]
    [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
    [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
    {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
    {L : Type} [Field L] [NumberField L] [IsCMField L]
    [IsQuadraticExtension ℚ L] [Algebra L F]
    {τ₀ : L →+* ℂ}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n
      (harrisCMSection E (algebraMap L F) τ₀))
    {S : Scheme.{0}} (p : S ⟶ Spec (.of F))
    (B : AbelianScheme S) (i : A →ₐ[ℚ] End0 B)
    {ι : Type} [Fintype ι] {U : S.Opens} {I : Type} [Fintype I]

local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀
local notation "b" => D.harrisTaylorReflexStructure C p
local notation "α" => D.harrisRationalOrderAction C B i

/-- The actual rational Lie polynomial uses `p`, with explicitly normalized CM coefficients. -/
def HarrisTaylorCMRationalLieDeterminantConditionAt
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (a : ι → D.harrisHodgePELIntegralOrder C) (V : Over U) : Prop :=
  lieRationalSectionDeterminant p B α e a V =
    MvPolynomial.map (secHom p V.left).hom
      (D.kottwitzReflexDeterminantBaseChange C hΦ (fun k => (a k : A))
        (D.harrisTaylorReflexToCM C).toRingHom)

/-- The single-CM-map local test is exactly the existing test at the normalized reflex base. -/
theorem harrisTaylorCMRationalLieDeterminantConditionAt_iff
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (a : ι → D.harrisHodgePELIntegralOrder C) (V : Over U) :
    D.HarrisTaylorCMRationalLieDeterminantConditionAt C p B i e a V ↔
      D.HarrisRationalLieDeterminantConditionAt C hΦ b B i e a V := by
  unfold HarrisTaylorCMRationalLieDeterminantConditionAt HarrisRationalLieDeterminantConditionAt
  rw [lieRationalSectionDeterminant_base_independent b p B α e a V,
    D.harrisReflexSectionDeterminant_harrisTaylor_CM C p a V.left]

/-- The same-map test retains equality of every coefficient in the actual section ring. -/
theorem harrisTaylorCMRationalLieDeterminantConditionAt_iff_coeff
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (a : ι → D.harrisHodgePELIntegralOrder C) (V : Over U) :
    D.HarrisTaylorCMRationalLieDeterminantConditionAt C p B i e a V ↔
      ∀ d : ι →₀ ℕ,
        (lieRationalSectionDeterminant p B α e a V).coeff d =
          (secHom p V.left).hom
            ((D.kottwitzReflexDeterminantBaseChange C hΦ (fun k => (a k : A))
              (D.harrisTaylorReflexToCM C).toRingHom).coeff d) := by
  simp only [HarrisTaylorCMRationalLieDeterminantConditionAt, MvPolynomial.ext_iff,
    MvPolynomial.coeff_map]

/-- The same-map local test restricts to every actual smaller open. -/
theorem harrisTaylorCMRationalLieDeterminantConditionAt_restrict
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (a : ι → D.harrisHodgePELIntegralOrder C) {V W : Over U} (j : V ⟶ W)
    (h : D.HarrisTaylorCMRationalLieDeterminantConditionAt C p B i e a W) :
    D.HarrisTaylorCMRationalLieDeterminantConditionAt C p B i e a V :=
  (D.harrisTaylorCMRationalLieDeterminantConditionAt_iff C p B i e a V).mpr
    (D.harrisRationalLieDeterminantConditionAt_restrict C hΦ b B i e a j
      ((D.harrisTaylorCMRationalLieDeterminantConditionAt_iff C p B i e a W).mp h))

/-- The determinant test through `p` on every finite family and every actual finite Lie chart. -/
def HarrisTaylorCMRationalLieDeterminantCondition : Prop :=
  ∀ (ι : Type) [Fintype ι] (a : ι → D.harrisHodgePELIntegralOrder C)
    (U : S.Opens) (I : Type) [Fintype I]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (V : Over U), D.HarrisTaylorCMRationalLieDeterminantConditionAt C p B i e a V

/-- The global single-map test is equivalent to the existing normalized-reflex-base test. -/
theorem harrisTaylorCMRationalLieDeterminantCondition_iff :
    D.HarrisTaylorCMRationalLieDeterminantCondition C p B i ↔
      D.HarrisRationalLieDeterminantCondition C hΦ b B i := by
  constructor
  · intro h ι _ a U I _ e V
    exact (D.harrisTaylorCMRationalLieDeterminantConditionAt_iff C p B i e a V).mp
      (h ι a U I e V)
  · intro h ι _ a U I _ e V
    exact (D.harrisTaylorCMRationalLieDeterminantConditionAt_iff C p B i e a V).mpr
      (h ι a U I e V)

variable {B}

/-- Actual equivariant rational isomorphisms preserve the global same-CM-map condition. -/
theorem harrisTaylorCMRationalLieDeterminantCondition_iso
    {B' : AbelianScheme S} (i' : A →ₐ[ℚ] End0 B')
    (e : Langlands.Rationalization.of B ≅ Langlands.Rationalization.of B')
    (he : ∀ a : A, comp0 B B B' (i a) e.hom = comp0 B B' B' e.hom (i' a)) :
    D.HarrisTaylorCMRationalLieDeterminantCondition C p B i ↔
      D.HarrisTaylorCMRationalLieDeterminantCondition C p B' i' :=
  (D.harrisTaylorCMRationalLieDeterminantCondition_iff C p B i).trans
    ((D.harrisRationalLieDeterminantCondition_iso C hΦ b i i' e he).trans
      (D.harrisTaylorCMRationalLieDeterminantCondition_iff C p B' i').symm)

variable (B) [IsCMField F]

/-- The normalized order-family condition gives the exact arithmetic section coefficient
whenever the central element is in the actual order. -/
theorem harrisTaylorCMRationalLieDeterminantConditionAt_centralCoefficient
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (a : F) (c : D.harrisHodgePELIntegralOrder C)
    (hc : (c : A) = algebraMap F A a) (V : Over U)
    (h : D.HarrisTaylorCMRationalLieDeterminantConditionAt C p B i e ![1, c] V) :
    HodgeDeterminant.traceCoefficient
      (lieRationalSectionDeterminant p B α e ![1, c] V) =
      HarrisTaylor.lieTraceSection L p n a V.left := by
  have hf : (fun k : Fin 2 => ((![1, c] k : D.harrisHodgePELIntegralOrder C) : A)) =
      ![1, algebraMap F A a] := by
    ext k
    fin_cases k <;> simp [hc]
  change lieRationalSectionDeterminant p B α e ![1, c] V = _ at h
  rw [h, hf]
  exact D.traceCoefficient_harrisTaylorCentralDeterminant_section C p a V.left

end Langlands.Shimura.CentralSimpleUnitaryData
