import Langlands.AbelianScheme.LieDeterminant
import Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof
import Langlands.Shimura.PEL.HarrisIntegralOrder
import Langlands.Shimura.PEL.HodgeDeterminantReflex

/-! # The Harris Lie determinant condition on actual scheme sections -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite MvPolynomial
open Langlands.AbelianScheme
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

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
    {ι : Type} [Fintype ι]

/-- Map the actual reflex determinant into the actual ring of sections on an open. -/
def harrisReflexSectionDeterminant
    (a : ι → D.harrisHodgePELIntegralOrder C) (W : S.Opens) :
    MvPolynomial ι Γ(S, W) :=
  D.kottwitzReflexDeterminantBaseChange C hΦ (fun i => (a i : A))
    (secHom s W).hom

@[simp]
theorem coeff_harrisReflexSectionDeterminant
    (a : ι → D.harrisHodgePELIntegralOrder C) (W : S.Opens) (d : ι →₀ ℕ) :
    (D.harrisReflexSectionDeterminant C hΦ s a W).coeff d =
      (secHom s W).hom
        ((D.kottwitzReflexDeterminant C hΦ (fun i => (a i : A))).coeff d) :=
  MvPolynomial.coeff_map _ _ _

/-- Both sides use the structure morphism of the same scheme. -/
theorem harrisReflexSectionDeterminant_restrict
    (a : ι → D.harrisHodgePELIntegralOrder C) {V W : S.Opens} (j : V ⟶ W) :
    MvPolynomial.map (S.presheaf.map j.op).hom
        (D.harrisReflexSectionDeterminant C hΦ s a W) =
      D.harrisReflexSectionDeterminant C hΦ s a V := by
  unfold harrisReflexSectionDeterminant kottwitzReflexDeterminantBaseChange
  rw [MvPolynomial.map_map]
  have hsec : (S.presheaf.map j.op).hom.comp (secHom s W).hom =
      (secHom s V).hom := by
    change (secHom s W ≫ S.presheaf.map j.op).hom = (secHom s V).hom
    have hj : j = homOfLE (leOfHom j) := Subsingleton.elim _ _
    rw [hj, secHom_map]
  rw [hsec]

@[simp]
theorem eval_harrisReflexSectionDeterminant
    (a : ι → D.harrisHodgePELIntegralOrder C) (W : S.Opens)
    (x : ι → Γ(S, W)) :
    eval x (D.harrisReflexSectionDeterminant C hΦ s a W) =
      eval₂ (secHom s W).hom x
        (D.kottwitzReflexDeterminant C hΦ (fun i => (a i : A))) :=
  MvPolynomial.eval_map _ _ _

variable (B : AbelianScheme S)
    (α : D.harrisHodgePELIntegralOrder C →+* Langlands.AbelianScheme.End B)
    {U : S.Opens} {I : Type} [Fintype I]

/-- Polynomial equality on actual Lie sections, as an additional moduli condition. -/
def HarrisLieDeterminantConditionAt
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (a : ι → D.harrisHodgePELIntegralOrder C) (V : Over U) : Prop :=
  lieSectionDeterminant B α e a V =
    D.harrisReflexSectionDeterminant C hΦ s a V.left

/-- The condition is equality of all actual structure-sheaf coefficients. -/
theorem harrisLieDeterminantConditionAt_iff_coeff
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (a : ι → D.harrisHodgePELIntegralOrder C) (V : Over U) :
    D.HarrisLieDeterminantConditionAt C hΦ s B α e a V ↔
      ∀ d : ι →₀ ℕ,
        (lieSectionDeterminant B α e a V).coeff d =
          (secHom s V.left).hom
            ((D.kottwitzReflexDeterminant C hΦ (fun i => (a i : A))).coeff d) := by
  simp only [HarrisLieDeterminantConditionAt, MvPolynomial.ext_iff,
    coeff_harrisReflexSectionDeterminant]

/-- Any finite basis of the actual section module gives the same condition. -/
theorem harrisLieDeterminantConditionAt_iff_basis
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (a : ι → D.harrisHodgePELIntegralOrder C) (V : Over U)
    {J : Type} [Fintype J] [DecidableEq J]
    (b : Module.Basis J Γ(S, V.left) Γ(B.Lie, V.left)) :
    D.HarrisLieDeterminantConditionAt C hΦ s B α e a V ↔
      HodgeDeterminant.polynomial b (fun i => lieSectionOrderAction B α V (a i)) =
        D.harrisReflexSectionDeterminant C hΦ s a V.left := by
  unfold HarrisLieDeterminantConditionAt
  rw [lieSectionDeterminant_eq_basis B α e a V b]

/-- Different charts impose the identical condition on their common smaller open. -/
theorem harrisLieDeterminantConditionAt_overlap
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    {U' T : S.Opens} {J : Type} [Fintype J]
    (e' : SheafOfModules.free (R := S.ringCatSheaf.over U') J ≅ B.Lie.over U')
    (a : ι → D.harrisHodgePELIntegralOrder C) (i : T ⟶ U) (j : T ⟶ U') :
    D.HarrisLieDeterminantConditionAt C hΦ s B α e a (Over.mk i) ↔
      D.HarrisLieDeterminantConditionAt C hΦ s B α e' a (Over.mk j) := by
  unfold HarrisLieDeterminantConditionAt
  change lieSectionDeterminant B α e a (Over.mk i) =
      D.harrisReflexSectionDeterminant C hΦ s a T ↔
    lieSectionDeterminant B α e' a (Over.mk j) =
      D.harrisReflexSectionDeterminant C hΦ s a T
  rw [lieSectionDeterminant_overlap B α e e' a i j]

/-- Polynomial equality is preserved by actual restriction to a smaller open. -/
theorem harrisLieDeterminantConditionAt_restrict
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (a : ι → D.harrisHodgePELIntegralOrder C) {V W : Over U} (j : V ⟶ W)
    (h : D.HarrisLieDeterminantConditionAt C hΦ s B α e a W) :
    D.HarrisLieDeterminantConditionAt C hΦ s B α e a V := by
  unfold HarrisLieDeterminantConditionAt at h ⊢
  rw [← lieSectionDeterminant_restrict B α e a j, h,
    harrisReflexSectionDeterminant_restrict]

/-- The polynomial condition gives the intrinsic determinant identity for every tuple. -/
theorem harrisLieDeterminantConditionAt_eval
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (a : ι → D.harrisHodgePELIntegralOrder C) (V : Over U)
    (h : D.HarrisLieDeterminantConditionAt C hΦ s B α e a V)
    (x : ι → Γ(S, V.left)) :
    LinearMap.det (∑ i, x i • lieSectionOrderAction B α V (a i)) =
      eval₂ (secHom s V.left).hom x
        (D.kottwitzReflexDeterminant C hΦ (fun i => (a i : A))) := by
  rw [← eval_lieSectionDeterminant B α e a V x, h]
  exact D.eval_harrisReflexSectionDeterminant C hΦ s a V.left x

/-- The condition can be checked on an arbitrary open covering of a chart open. -/
theorem harrisLieDeterminantConditionAt_of_cover
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (a : ι → D.harrisHodgePELIntegralOrder C) (V : Over U)
    {κ : Type*} (W : κ → S.Opens) (iW : ∀ k, W k ⟶ V.left)
    (hcov : V.left ≤ iSup W)
    (h : ∀ k, D.HarrisLieDeterminantConditionAt C hΦ s B α e a
      (Over.mk (iW k ≫ V.hom))) :
    D.HarrisLieDeterminantConditionAt C hΦ s B α e a V := by
  apply MvPolynomial.ext
  intro d
  apply S.sheaf.eq_of_locally_eq' W V.left iW hcov
  intro k
  change (S.presheaf.map (iW k).op).hom
      ((lieSectionDeterminant B α e a V).coeff d) =
    (S.presheaf.map (iW k).op).hom
      ((D.harrisReflexSectionDeterminant C hΦ s a V.left).coeff d)
  let j : Over.mk (iW k ≫ V.hom) ⟶ V := Over.homMk (iW k)
  have hk :
      MvPolynomial.map (S.presheaf.map (iW k).op).hom
          (lieSectionDeterminant B α e a V) =
        MvPolynomial.map (S.presheaf.map (iW k).op).hom
          (D.harrisReflexSectionDeterminant C hΦ s a V.left) := by
    calc
      _ = lieSectionDeterminant B α e a (Over.mk (iW k ≫ V.hom)) :=
        lieSectionDeterminant_restrict B α e a j
      _ = D.harrisReflexSectionDeterminant C hΦ s a (W k) := h k
      _ = _ := (D.harrisReflexSectionDeterminant_restrict C hΦ s a (iW k)).symm
  simpa only [MvPolynomial.coeff_map] using congrArg (fun p => p.coeff d) hk

/-- The actual characteristic-zero determinant condition, on every finite Lie chart. -/
def HarrisLieDeterminantCondition : Prop :=
  ∀ (ι : Type) [Fintype ι] (a : ι → D.harrisHodgePELIntegralOrder C)
    (U : S.Opens) (I : Type) [Fintype I]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (V : Over U), D.HarrisLieDeterminantConditionAt C hΦ s B α e a V

/-- A global condition applies in particular to the genuinely constructed Lie cover. -/
theorem harrisLieDeterminantCondition_chart
    (h : D.HarrisLieDeterminantCondition C hΦ s B α)
    (a : ι → D.harrisHodgePELIntegralOrder C) (i : (lieFiniteLocalBasisData B).I)
    (V : Over ((lieFiniteLocalBasisData B).X i)) :
    lieChartDeterminant B α a i V =
      D.harrisReflexSectionDeterminant C hΦ s a V.left :=
  h ι a _ _ (lieFiniteLocalBasisTrivialization B i) V

/-- It suffices to check the whole opens of the proved Lie covering. -/
theorem harrisLieDeterminantCondition_iff_cover :
    D.HarrisLieDeterminantCondition C hΦ s B α ↔
      ∀ (ι : Type) [Fintype ι] (a : ι → D.harrisHodgePELIntegralOrder C)
        (i : (lieFiniteLocalBasisData B).I),
        lieChartDeterminant B α a i (Over.mk (𝟙 _)) =
          D.harrisReflexSectionDeterminant C hΦ s a
            ((lieFiniteLocalBasisData B).X i) := by
  constructor
  · intro h ι _ a i
    exact D.harrisLieDeterminantCondition_chart C hΦ s B α h a i _
  · intro h ι _ a U I _ e V
    let q := lieFiniteLocalBasisData B
    have hq : (⨆ i, q.X i) = ⊤ := by
      have hcover := q.coversTop
      rwa [_root_.Opens.coversTop_iff, TopologicalSpace.IsOpenCover] at hcover
    apply D.harrisLieDeterminantConditionAt_of_cover C hΦ s B α e a V
      (fun i => V.left ⊓ q.X i) (fun _ => homOfLE inf_le_left)
    · intro x hx
      have hxq : x ∈ ⨆ i, q.X i := by rw [hq]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxq
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hx, hi⟩
    · intro i
      let e' := lieFiniteLocalBasisTrivialization B i
      have hi : D.HarrisLieDeterminantConditionAt C hΦ s B α e' a
          (Over.mk (𝟙 (q.X i))) := h ι a i
      have hsmall := D.harrisLieDeterminantConditionAt_restrict C hΦ s B α e' a
        (Over.homMk (homOfLE inf_le_right) :
          Over.mk (homOfLE (inf_le_right : V.left ⊓ q.X i ≤ q.X i)) ⟶
            Over.mk (𝟙 (q.X i))) hi
      exact (D.harrisLieDeterminantConditionAt_overlap C hΦ s B α e e' a
        (homOfLE inf_le_left ≫ V.hom) (homOfLE inf_le_right)).mpr hsmall

end Langlands.Shimura.CentralSimpleUnitaryData
