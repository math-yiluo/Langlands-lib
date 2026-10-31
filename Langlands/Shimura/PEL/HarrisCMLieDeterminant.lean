import Langlands.Shimura.PEL.HarrisReflexBase
import Langlands.Shimura.PEL.RationalLieDeterminantCondition
import Langlands.AbelianScheme.LieRationalBaseIndependence

/-! # The Harris rational Lie determinant condition through one CM structure map -/

noncomputable section

open CategoryTheory AlgebraicGeometry
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
local notation "b" => D.harrisReflexStructure C p
local notation "α" => D.harrisRationalOrderAction C B i

/-- Both the actual rational Lie polynomial and its prescribed coefficients use `p`. -/
def HarrisCMRationalLieDeterminantConditionAt
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (a : ι → D.harrisHodgePELIntegralOrder C) (V : Over U) : Prop :=
  lieRationalSectionDeterminant p B α e a V =
    MvPolynomial.map (secHom p V.left).hom
      (D.kottwitzReflexDeterminantBaseChange C hΦ (fun k => (a k : A))
        (D.harrisReflexToCM C).toRingHom)

/-- The single-CM-map local test is exactly the existing test at the constructed reflex base. -/
theorem harrisCMRationalLieDeterminantConditionAt_iff
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (a : ι → D.harrisHodgePELIntegralOrder C) (V : Over U) :
    D.HarrisCMRationalLieDeterminantConditionAt C p B i e a V ↔
      D.HarrisRationalLieDeterminantConditionAt C hΦ b B i e a V := by
  unfold HarrisCMRationalLieDeterminantConditionAt HarrisRationalLieDeterminantConditionAt
  rw [lieRationalSectionDeterminant_base_independent b p B α e a V,
    D.harrisReflexSectionDeterminant_CM C p a V.left]

/-- The same-map test retains equality of every coefficient in the actual section ring. -/
theorem harrisCMRationalLieDeterminantConditionAt_iff_coeff
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (a : ι → D.harrisHodgePELIntegralOrder C) (V : Over U) :
    D.HarrisCMRationalLieDeterminantConditionAt C p B i e a V ↔
      ∀ d : ι →₀ ℕ,
        (lieRationalSectionDeterminant p B α e a V).coeff d =
          (secHom p V.left).hom
            ((D.kottwitzReflexDeterminantBaseChange C hΦ (fun k => (a k : A))
              (D.harrisReflexToCM C).toRingHom).coeff d) := by
  simp only [HarrisCMRationalLieDeterminantConditionAt, MvPolynomial.ext_iff,
    MvPolynomial.coeff_map]

/-- The same-map local test restricts to every actual smaller open. -/
theorem harrisCMRationalLieDeterminantConditionAt_restrict
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (a : ι → D.harrisHodgePELIntegralOrder C) {V W : Over U} (j : V ⟶ W)
    (h : D.HarrisCMRationalLieDeterminantConditionAt C p B i e a W) :
    D.HarrisCMRationalLieDeterminantConditionAt C p B i e a V :=
  (D.harrisCMRationalLieDeterminantConditionAt_iff C p B i e a V).mpr
    (D.harrisRationalLieDeterminantConditionAt_restrict C hΦ b B i e a j
      ((D.harrisCMRationalLieDeterminantConditionAt_iff C p B i e a W).mp h))

/-- The determinant test through `p` on every finite family and every actual finite Lie chart. -/
def HarrisCMRationalLieDeterminantCondition : Prop :=
  ∀ (ι : Type) [Fintype ι] (a : ι → D.harrisHodgePELIntegralOrder C)
    (U : S.Opens) (I : Type) [Fintype I]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (V : Over U), D.HarrisCMRationalLieDeterminantConditionAt C p B i e a V

/-- The global single-map test is equivalent to the existing constructed-reflex-base test. -/
theorem harrisCMRationalLieDeterminantCondition_iff :
    D.HarrisCMRationalLieDeterminantCondition C p B i ↔
      D.HarrisRationalLieDeterminantCondition C hΦ b B i := by
  constructor
  · intro h ι _ a U I _ e V
    exact (D.harrisCMRationalLieDeterminantConditionAt_iff C p B i e a V).mp
      (h ι a U I e V)
  · intro h ι _ a U I _ e V
    exact (D.harrisCMRationalLieDeterminantConditionAt_iff C p B i e a V).mpr
      (h ι a U I e V)

variable {B}

/-- Actual equivariant rational isomorphisms preserve the global same-CM-map condition. -/
theorem harrisCMRationalLieDeterminantCondition_iso
    {B' : AbelianScheme S} (i' : A →ₐ[ℚ] End0 B')
    (e : Langlands.Rationalization.of B ≅ Langlands.Rationalization.of B')
    (he : ∀ a : A, comp0 B B B' (i a) e.hom = comp0 B B' B' e.hom (i' a)) :
    D.HarrisCMRationalLieDeterminantCondition C p B i ↔
      D.HarrisCMRationalLieDeterminantCondition C p B' i' :=
  (D.harrisCMRationalLieDeterminantCondition_iff C p B i).trans
    ((D.harrisRationalLieDeterminantCondition_iso C hΦ b i i' e he).trans
      (D.harrisCMRationalLieDeterminantCondition_iff C p B' i').symm)

end Langlands.Shimura.CentralSimpleUnitaryData
