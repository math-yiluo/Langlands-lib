import Langlands.AbelianScheme.LieRationalDeterminant
import Langlands.Shimura.PEL.LieDeterminantCondition

/-! # The Harris section determinant condition for actual rational algebra actions -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite MvPolynomial
open Langlands.AbelianScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField _root_.Algebra

variable {E K A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
    {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
    {Φ : (E →+* ℝ) → (K →+* ℂ)}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
    (hΦ : IsCMSection E K Φ)
    {S : AlgebraicGeometry.Scheme.{0}}
    (s : S ⟶ Spec (CommRingCat.of (D.kottwitzCocharacterReflexField C)))

/-- Restrict an actual rational algebra action to the constructed Harris order. -/
def harrisRationalOrderAction (B : AbelianScheme S) (i : A →ₐ[ℚ] End0 B) :
    D.harrisHodgePELIntegralOrder C →+* End0 B :=
  i.toRingHom.comp (D.harrisHodgePELIntegralOrder C).subtype

omit [IsScalarTower ℚ K A] in
@[simp]
theorem harrisRationalOrderAction_apply (B : AbelianScheme S)
    (i : A →ₐ[ℚ] End0 B) (a : D.harrisHodgePELIntegralOrder C) :
    D.harrisRationalOrderAction C B i a = i (a : A) := rfl

variable (B : AbelianScheme S) (i : A →ₐ[ℚ] End0 B)
    {ι : Type} [Fintype ι] {U : S.Opens} {I : Type} [Fintype I]

/-- Equality of the actual rational Lie polynomial and the same reflex polynomial. -/
def HarrisRationalLieDeterminantConditionAt
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (a : ι → D.harrisHodgePELIntegralOrder C) (V : Over U) : Prop :=
  lieRationalSectionDeterminant s B (D.harrisRationalOrderAction C B i) e a V =
    D.harrisReflexSectionDeterminant C hΦ s a V.left

/-- The rational condition retains equality of every actual structure-sheaf coefficient. -/
theorem harrisRationalLieDeterminantConditionAt_iff_coeff
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (a : ι → D.harrisHodgePELIntegralOrder C) (V : Over U) :
    D.HarrisRationalLieDeterminantConditionAt C hΦ s B i e a V ↔
      ∀ d : ι →₀ ℕ,
        (lieRationalSectionDeterminant s B (D.harrisRationalOrderAction C B i)
          e a V).coeff d =
        (Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof.secHom
          s V.left).hom
          ((D.kottwitzReflexDeterminant C hΦ (fun k => (a k : A))).coeff d) := by
  simp only [HarrisRationalLieDeterminantConditionAt, MvPolynomial.ext_iff,
    coeff_harrisReflexSectionDeterminant]

/-- The rational condition restricts along every actual inclusion of smaller opens. -/
theorem harrisRationalLieDeterminantConditionAt_restrict
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (a : ι → D.harrisHodgePELIntegralOrder C) {V W : Over U} (j : V ⟶ W)
    (h : D.HarrisRationalLieDeterminantConditionAt C hΦ s B i e a W) :
    D.HarrisRationalLieDeterminantConditionAt C hΦ s B i e a V := by
  unfold HarrisRationalLieDeterminantConditionAt at h ⊢
  rw [← lieRationalSectionDeterminant_restrict s B _ e a j, h,
    harrisReflexSectionDeterminant_restrict]

/-- The condition specializes to the intrinsic determinant identity for every tuple. -/
theorem harrisRationalLieDeterminantConditionAt_eval
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (a : ι → D.harrisHodgePELIntegralOrder C) (V : Over U)
    (h : D.HarrisRationalLieDeterminantConditionAt C hΦ s B i e a V)
    (x : ι → Γ(S, V.left)) :
    LinearMap.det (∑ k, x k •
        lieRationalSectionOrderAction s B (D.harrisRationalOrderAction C B i) V (a k)) =
      eval₂
        (Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof.secHom
          s V.left).hom x
        (D.kottwitzReflexDeterminant C hΦ (fun k => (a k : A))) := by
  rw [← eval_lieRationalSectionDeterminant s B _ e a V x, h]
  exact D.eval_harrisReflexSectionDeterminant C hΦ s a V.left x

/-- Compatibility with an actual integral action recovers the existing local condition. -/
theorem harrisRationalLieDeterminantConditionAt_iff_integral
    (α : D.harrisHodgePELIntegralOrder C →+* Langlands.AbelianScheme.End B)
    (hα : ∀ a, endToEnd0 B (α a) = i (a : A))
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (a : ι → D.harrisHodgePELIntegralOrder C) (V : Over U) :
    D.HarrisRationalLieDeterminantConditionAt C hΦ s B i e a V ↔
      D.HarrisLieDeterminantConditionAt C hΦ s B α e a V := by
  have ha : D.harrisRationalOrderAction C B i = (endToEnd0 B).comp α := by
    ext a
    exact (hα a).symm
  unfold HarrisRationalLieDeterminantConditionAt HarrisLieDeterminantConditionAt
  rw [ha, lieRationalSectionDeterminant_integral]

/-- The rational condition requires every finite family, finite Lie chart and smaller open. -/
def HarrisRationalLieDeterminantCondition : Prop :=
  ∀ (ι : Type) [Fintype ι] (a : ι → D.harrisHodgePELIntegralOrder C)
    (U : S.Opens) (I : Type) [Fintype I]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (V : Over U), D.HarrisRationalLieDeterminantConditionAt C hΦ s B i e a V

/-- When the actions agree, the global rational and integral conditions are equivalent. -/
theorem harrisRationalLieDeterminantCondition_iff_integral
    (α : D.harrisHodgePELIntegralOrder C →+* Langlands.AbelianScheme.End B)
    (hα : ∀ a, endToEnd0 B (α a) = i (a : A)) :
    D.HarrisRationalLieDeterminantCondition C hΦ s B i ↔
      D.HarrisLieDeterminantCondition C hΦ s B α := by
  constructor
  · intro h ι _ a U I _ e V
    exact (D.harrisRationalLieDeterminantConditionAt_iff_integral C hΦ s B i
      α hα e a V).mp (h ι a U I e V)
  · intro h ι _ a U I _ e V
    exact (D.harrisRationalLieDeterminantConditionAt_iff_integral C hΦ s B i
      α hα e a V).mpr (h ι a U I e V)

variable {B}

/-- An actual intertwining rational isomorphism preserves the local condition in any charts. -/
theorem harrisRationalLieDeterminantConditionAt_iso
    {B' : AbelianScheme S} (i' : A →ₐ[ℚ] End0 B')
    (e : Langlands.Rationalization.of B ≅ Langlands.Rationalization.of B')
    (he : ∀ a : A, comp0 B B B' (i a) e.hom = comp0 B B' B' e.hom (i' a))
    (eB : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    {J : Type} [Fintype J]
    (eB' : SheafOfModules.free (R := S.ringCatSheaf.over U) J ≅ B'.Lie.over U)
    (a : ι → D.harrisHodgePELIntegralOrder C) (V : Over U) :
    D.HarrisRationalLieDeterminantConditionAt C hΦ s B i eB a V ↔
      D.HarrisRationalLieDeterminantConditionAt C hΦ s B' i' eB' a V := by
  unfold HarrisRationalLieDeterminantConditionAt
  rw [lieRationalSectionDeterminant_iso s (D.harrisRationalOrderAction C B i)
    (D.harrisRationalOrderAction C B' i') e (fun a => he (a : A)) eB eB' a V]

/-- Rational isomorphism invariance holds on all charts, including unselected target charts. -/
theorem harrisRationalLieDeterminantCondition_iso
    {B' : AbelianScheme S} (i' : A →ₐ[ℚ] End0 B')
    (e : Langlands.Rationalization.of B ≅ Langlands.Rationalization.of B')
    (he : ∀ a : A, comp0 B B B' (i a) e.hom = comp0 B B' B' e.hom (i' a)) :
    D.HarrisRationalLieDeterminantCondition C hΦ s B i ↔
      D.HarrisRationalLieDeterminantCondition C hΦ s B' i' := by
  constructor
  · intro h ι _ a U I _ eB' V
    let eB := eB' ≪≫ (lieLocalIso0 s e U).symm
    exact (D.harrisRationalLieDeterminantConditionAt_iso C hΦ s i i'
      e he eB eB' a V).mp (h ι a U I eB V)
  · intro h ι _ a U I _ eB V
    let eB' := eB ≪≫ lieLocalIso0 s e U
    exact (D.harrisRationalLieDeterminantConditionAt_iso C hΦ s i i'
      e he eB eB' a V).mpr (h ι a U I eB' V)

end Langlands.Shimura.CentralSimpleUnitaryData
