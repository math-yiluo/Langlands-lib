import Langlands.AlgebraicGeometry.LocalDeterminantTransport
import Langlands.AbelianScheme.LieOrderBaseChange
import Langlands.Shimura.PEL.ReflexSectionPullback

/-! # Actual base-changed Lie charts and conditional determinant stability -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w

namespace Langlands.AbelianScheme

variable {S T : AlgebraicGeometry.Scheme.{u}} (b : T ⟶ S)
    (B : AbelianScheme S) {U : S.Opens} {I : Type u} [Fintype I]

/-- Pull back an actual finite Lie chart and transport by the uniquely characterized Lie iso. -/
def lieBaseChangeChart
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U) :
    SheafOfModules.free (R := T.ringCatSheaf.over (b ⁻¹ᵁ U)) I ≅
      ((baseChange b).obj B).Lie.over (b ⁻¹ᵁ U) :=
  chartFreePullbackTransportIso b e
    ((SheafOfModules.overFunctor T.ringCatSheaf (b ⁻¹ᵁ U)).mapIso
      (lieBaseChangeIso b B))

variable {O : Type v} [Ring O] (α : O →+* End B)
    {ι : Type w} [Fintype ι]

/-- Determinants on the constructed actual Lie charts, conditional on order-action naturality. -/
theorem lieSectionDeterminant_baseChange_of_intertwine
    (hα : ∀ x : O,
      (AlgebraicGeometry.Scheme.Modules.pullback b).map (lieOrderAction B α x) ≫
          (lieBaseChangeIso b B).hom =
        (lieBaseChangeIso b B).hom ≫
          lieOrderAction ((baseChange b).obj B) (baseChangeOrderAction b B α) x)
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (a : ι → O) (V : Over U) :
    MvPolynomial.map (b.app V.left).hom (lieSectionDeterminant B α e a V) =
      lieSectionDeterminant ((baseChange b).obj B) (baseChangeOrderAction b B α)
        (lieBaseChangeChart b B e) a
        (Over.mk ((TopologicalSpace.Opens.map b.base).map V.hom)) := by
  apply localSectionDeterminant_pullback_transport
  intro i
  exact localHomPullback_over_intertwine b (lieBaseChangeIso b B)
    (lieOrderAction B α (a i))
    (lieOrderAction ((baseChange b).obj B) (baseChangeOrderAction b B α) (a i))
    (hα (a i)) U

end Langlands.AbelianScheme

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField _root_.Algebra Langlands.AbelianScheme

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
    {S T : AlgebraicGeometry.Scheme.{0}}
    (s : S ⟶ Spec (CommRingCat.of (D.kottwitzCocharacterReflexField C)))
    (b : T ⟶ S) (B : AbelianScheme S)
    (α : D.harrisHodgePELIntegralOrder C →+* Langlands.AbelianScheme.End B)
    (hα : ∀ x : D.harrisHodgePELIntegralOrder C,
      (AlgebraicGeometry.Scheme.Modules.pullback b).map (lieOrderAction B α x) ≫
          (lieBaseChangeIso b B).hom =
        (lieBaseChangeIso b B).hom ≫
          lieOrderAction ((baseChange b).obj B) (baseChangeOrderAction b B α) x)

include hα

/-- The actual Harris condition transports first to each constructed inverse-image chart. -/
theorem harrisLieDeterminantConditionAt_baseChange_of_intertwine
    {ι : Type} [Fintype ι] {U : S.Opens} {I : Type} [Fintype I]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (a : ι → D.harrisHodgePELIntegralOrder C) (V : Over U)
    (h : D.HarrisLieDeterminantConditionAt C hΦ s B α e a V) :
    D.HarrisLieDeterminantConditionAt C hΦ (b ≫ s)
      ((baseChange b).obj B) (baseChangeOrderAction b B α)
      (lieBaseChangeChart b B e) a
      (Over.mk ((TopologicalSpace.Opens.map b.base).map V.hom)) := by
  unfold HarrisLieDeterminantConditionAt at h ⊢
  rw [← lieSectionDeterminant_baseChange_of_intertwine b B α hα e a V, h]
  exact D.harrisReflexSectionDeterminant_pullback C hΦ s b a V.left

/-- Cover descent gives every target chart, conditional only on actual Lie-action intertwining. -/
theorem harrisLieDeterminantCondition_baseChange_of_intertwine
    (h : D.HarrisLieDeterminantCondition C hΦ s B α) :
    D.HarrisLieDeterminantCondition C hΦ (b ≫ s)
      ((baseChange b).obj B) (baseChangeOrderAction b B α) := by
  intro ι _ a U I _ e V
  let q := lieFiniteLocalBasisData B
  have hq : (⨆ i, q.X i) = ⊤ := by
    have hcover := q.coversTop
    rwa [_root_.Opens.coversTop_iff, TopologicalSpace.IsOpenCover] at hcover
  apply D.harrisLieDeterminantConditionAt_of_cover C hΦ (b ≫ s)
    ((baseChange b).obj B) (baseChangeOrderAction b B α) e a V
    (fun i => V.left ⊓ b ⁻¹ᵁ q.X i) (fun _ => homOfLE inf_le_left)
  · intro x hx
    have hxq : b.base x ∈ ⨆ i, q.X i := by rw [hq]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxq
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hx, hi⟩
  · intro i
    let e' := lieBaseChangeChart b B (lieFiniteLocalBasisTrivialization B i)
    have hi := D.harrisLieDeterminantConditionAt_baseChange_of_intertwine
      C hΦ s b B α hα (lieFiniteLocalBasisTrivialization B i) a (Over.mk (𝟙 _))
      (h ι a _ _ (lieFiniteLocalBasisTrivialization B i) (Over.mk (𝟙 _)))
    have hi' : D.HarrisLieDeterminantConditionAt C hΦ (b ≫ s)
        ((baseChange b).obj B) (baseChangeOrderAction b B α) e' a
        (Over.mk (𝟙 (b ⁻¹ᵁ q.X i))) := by
      exact hi
    have hsmall := D.harrisLieDeterminantConditionAt_restrict C hΦ (b ≫ s)
      ((baseChange b).obj B) (baseChangeOrderAction b B α) e' a
      (Over.homMk (homOfLE inf_le_right) :
        Over.mk (homOfLE (inf_le_right : V.left ⊓ b ⁻¹ᵁ q.X i ≤ b ⁻¹ᵁ q.X i)) ⟶
          Over.mk (𝟙 (b ⁻¹ᵁ q.X i))) hi'
    exact (D.harrisLieDeterminantConditionAt_overlap C hΦ (b ≫ s)
      ((baseChange b).obj B) (baseChangeOrderAction b B α) e e' a
      (homOfLE inf_le_left ≫ V.hom) (homOfLE inf_le_right)).mpr hsmall

end Langlands.Shimura.CentralSimpleUnitaryData
