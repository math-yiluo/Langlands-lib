import Langlands.AbelianScheme.LieRationalBaseChange
import Langlands.Shimura.PEL.LieDeterminantBaseChange
import Langlands.Shimura.PEL.RationalLieDeterminantClasses
import Mathlib.CategoryTheory.Subfunctor.Basic

/-! # Rational Harris determinant pullback and its actual moduli subpresheaf -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.Scheme.Modules

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w

namespace Langlands.AbelianScheme

variable {S T : Scheme.{u}} {R : CommRingCat.{u}} [Algebra ℚ R]
    (p : S ⟶ Spec R) (b : T ⟶ S) (B : AbelianScheme S)
    {O : Type v} [Ring O] (α : O →+* End0 B)
    {ι : Type w} [Fintype ι]

/-- Actual rational Lie polynomials agree on every common smaller chart open. -/
theorem lieRationalSectionDeterminant_overlap
    {U U' W : S.Opens} {I J : Type u} [Fintype I] [Fintype J]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (e' : SheafOfModules.free (R := S.ringCatSheaf.over U') J ≅ B.Lie.over U')
    (a : ι → O) (i : W ⟶ U) (j : W ⟶ U') :
    lieRationalSectionDeterminant p B α e a (Over.mk i) =
      lieRationalSectionDeterminant p B α e' a (Over.mk j) := by
  let : DecidableEq I := Classical.decEq I
  let : DecidableEq J := Classical.decEq J
  exact Langlands.Shimura.HodgeDeterminant.polynomial_basis_independent_commRing
    (localSectionBasis e (Over.mk i)) (localSectionBasis e' (Over.mk j))
    (fun k => (lieMap0 p (α (a k))).val.app (op W) |>.hom)

variable (naturality : LieBaseChangeNaturalityStatement S)

include naturality

/-- Canonical integral naturality gives actual rational Lie polynomial pullback. -/
theorem lieRationalSectionDeterminant_baseChange_of_naturality
    {U : S.Opens} {I : Type u} [Fintype I]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (a : ι → O) (V : Over U) :
    MvPolynomial.map (b.app V.left).hom (lieRationalSectionDeterminant p B α e a V) =
      lieRationalSectionDeterminant (b ≫ p) ((baseChange b).obj B)
        (baseChangeRationalOrderAction b B α) (lieBaseChangeChart b B e) a
        (Over.mk ((TopologicalSpace.Opens.map b.base).map V.hom)) := by
  apply localSectionDeterminant_pullback_transport
  intro k
  exact localHomPullback_over_intertwine b (lieBaseChangeIso b B)
    (lieRationalOrderAction p B α (a k))
    (lieRationalOrderAction (b ≫ p) ((baseChange b).obj B)
      (baseChangeRationalOrderAction b B α) (a k))
    (lieRationalOrderAction_baseChange_of_naturality p b naturality B α (a k)) U

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
    {S T : Scheme.{0}}
    (s : S ⟶ Spec (CommRingCat.of (D.kottwitzCocharacterReflexField C)))
    (B : AbelianScheme S) (i : A →ₐ[ℚ] End0 B)
    {ι : Type} [Fintype ι] {U : S.Opens} {I : Type} [Fintype I]

/-- Rational determinant conditions agree on the overlap of any two actual Lie charts. -/
theorem harrisRationalLieDeterminantConditionAt_overlap
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    {U' W : S.Opens} {J : Type} [Fintype J]
    (e' : SheafOfModules.free (R := S.ringCatSheaf.over U') J ≅ B.Lie.over U')
    (a : ι → D.harrisHodgePELIntegralOrder C) (j : W ⟶ U) (j' : W ⟶ U') :
    D.HarrisRationalLieDeterminantConditionAt C hΦ s B i e a (Over.mk j) ↔
      D.HarrisRationalLieDeterminantConditionAt C hΦ s B i e' a (Over.mk j') := by
  unfold HarrisRationalLieDeterminantConditionAt
  rw [lieRationalSectionDeterminant_overlap s B _ e e' a j j']
  rfl

/-- Coefficientwise sheaf separation checks the rational determinant test on an open cover. -/
theorem harrisRationalLieDeterminantConditionAt_of_cover
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (a : ι → D.harrisHodgePELIntegralOrder C) (V : Over U)
    {κ : Type*} (W : κ → S.Opens) (jW : ∀ k, W k ⟶ V.left)
    (hcov : V.left ≤ iSup W)
    (h : ∀ k, D.HarrisRationalLieDeterminantConditionAt C hΦ s B i e a
      (Over.mk (jW k ≫ V.hom))) :
    D.HarrisRationalLieDeterminantConditionAt C hΦ s B i e a V := by
  apply MvPolynomial.ext
  intro d
  apply S.sheaf.eq_of_locally_eq' W V.left jW hcov
  intro k
  change (S.presheaf.map (jW k).op).hom
      ((lieRationalSectionDeterminant s B (D.harrisRationalOrderAction C B i)
        e a V).coeff d) =
    (S.presheaf.map (jW k).op).hom
      ((D.harrisReflexSectionDeterminant C hΦ s a V.left).coeff d)
  let j : Over.mk (jW k ≫ V.hom) ⟶ V := Over.homMk (jW k)
  have hk :
      MvPolynomial.map (S.presheaf.map (jW k).op).hom
          (lieRationalSectionDeterminant s B (D.harrisRationalOrderAction C B i)
            e a V) =
        MvPolynomial.map (S.presheaf.map (jW k).op).hom
          (D.harrisReflexSectionDeterminant C hΦ s a V.left) := by
    calc
      _ = lieRationalSectionDeterminant s B (D.harrisRationalOrderAction C B i)
          e a (Over.mk (jW k ≫ V.hom)) :=
        lieRationalSectionDeterminant_restrict s B _ e a j
      _ = D.harrisReflexSectionDeterminant C hΦ s a (W k) := h k
      _ = _ := (D.harrisReflexSectionDeterminant_restrict C hΦ s a (jW k)).symm
  simpa only [MvPolynomial.coeff_map] using congrArg (fun p => p.coeff d) hk

variable (b : T ⟶ S)

omit [IsScalarTower ℚ K A] in
/-- The actual pulled-back algebra action restricts to the actual pulled-back Harris order. -/
theorem harrisRationalOrderAction_baseChange :
    D.harrisRationalOrderAction C ((baseChange b).obj B)
        ((rationalBaseChangeEnd b B).comp i) =
      baseChangeRationalOrderAction b B (D.harrisRationalOrderAction C B i) := rfl

variable (naturality : LieBaseChangeNaturalityStatement S)

include naturality

/-- The rational Harris determinant test pulls back to the constructed inverse-image chart. -/
theorem harrisRationalLieDeterminantConditionAt_baseChange_of_naturality
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (a : ι → D.harrisHodgePELIntegralOrder C) (V : Over U)
    (h : D.HarrisRationalLieDeterminantConditionAt C hΦ s B i e a V) :
    D.HarrisRationalLieDeterminantConditionAt C hΦ (b ≫ s)
      ((baseChange b).obj B) ((rationalBaseChangeEnd b B).comp i)
      (lieBaseChangeChart b B e) a
      (Over.mk ((TopologicalSpace.Opens.map b.base).map V.hom)) := by
  unfold HarrisRationalLieDeterminantConditionAt at h ⊢
  rw [harrisRationalOrderAction_baseChange,
    ← lieRationalSectionDeterminant_baseChange_of_naturality s b B _ naturality e a V, h]
  exact D.harrisReflexSectionDeterminant_pullback C hΦ s b a V.left

/-- The rational determinant test survives arbitrary base change on every target chart. -/
theorem harrisRationalLieDeterminantCondition_baseChange_of_naturality
    (h : D.HarrisRationalLieDeterminantCondition C hΦ s B i) :
    D.HarrisRationalLieDeterminantCondition C hΦ (b ≫ s)
      ((baseChange b).obj B) ((rationalBaseChangeEnd b B).comp i) := by
  intro ι _ a U I _ e V
  let q := lieFiniteLocalBasisData B
  have hq : (⨆ k, q.X k) = ⊤ := by
    have hcover := q.coversTop
    rwa [_root_.Opens.coversTop_iff, TopologicalSpace.IsOpenCover] at hcover
  apply D.harrisRationalLieDeterminantConditionAt_of_cover C hΦ (b ≫ s)
    ((baseChange b).obj B) ((rationalBaseChangeEnd b B).comp i) e a V
    (fun k => V.left ⊓ b ⁻¹ᵁ q.X k) (fun _ => homOfLE inf_le_left)
  · intro x hx
    have hxq : b.base x ∈ ⨆ k, q.X k := by rw [hq]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hxq
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨k, hx, hk⟩
  · intro k
    let e' := lieBaseChangeChart b B (lieFiniteLocalBasisTrivialization B k)
    have hk := D.harrisRationalLieDeterminantConditionAt_baseChange_of_naturality
      C hΦ s B i b naturality (lieFiniteLocalBasisTrivialization B k) a (Over.mk (𝟙 _))
      (h ι a _ _ (lieFiniteLocalBasisTrivialization B k) (Over.mk (𝟙 _)))
    have hk' : D.HarrisRationalLieDeterminantConditionAt C hΦ (b ≫ s)
        ((baseChange b).obj B) ((rationalBaseChangeEnd b B).comp i) e' a
        (Over.mk (𝟙 (b ⁻¹ᵁ q.X k))) := hk
    have hsmall := D.harrisRationalLieDeterminantConditionAt_restrict C hΦ (b ≫ s)
      ((baseChange b).obj B) ((rationalBaseChangeEnd b B).comp i) e' a
      (Over.homMk (homOfLE inf_le_right) :
        Over.mk (homOfLE (inf_le_right : V.left ⊓ b ⁻¹ᵁ q.X k ≤ b ⁻¹ᵁ q.X k)) ⟶
          Over.mk (𝟙 (b ⁻¹ᵁ q.X k))) hk'
    exact (D.harrisRationalLieDeterminantConditionAt_overlap C hΦ (b ≫ s)
      ((baseChange b).obj B) ((rationalBaseChangeEnd b B).comp i) e e' a
      (homOfLE inf_le_left ≫ V.hom) (homOfLE inf_le_right)).mpr hsmall

/-- The existing determinant predicate on actual rational action classes survives pullback. -/
theorem harrisRationalLieDeterminantClassCondition_baseChange_of_naturality
    (q : RationalAlgebraAction.IsoClass S A)
    (h : D.HarrisRationalLieDeterminantClassCondition C hΦ s q) :
    D.HarrisRationalLieDeterminantClassCondition C hΦ (b ≫ s)
      (RationalAlgebraAction.pullbackClass b q) := by
  obtain ⟨X, rfl⟩ := RationalAlgebraAction.classOf_surjective q
  exact D.harrisRationalLieDeterminantCondition_baseChange_of_naturality
    C hΦ s X.abelianScheme X.action b naturality h

omit naturality

/-- Actual determinant-compatible rational action classes as a subfunctor over the reflex base. -/
def harrisRationalLieDeterminantSubfunctor
    (allNaturality : ∀ X : Scheme.{0}, LieBaseChangeNaturalityStatement X) :
    Subfunctor (RationalAlgebraAction.isoClassOverPresheaf
      (Spec (CommRingCat.of (D.kottwitzCocharacterReflexField C))) A) where
  obj X := {q | D.HarrisRationalLieDeterminantClassCondition C hΦ X.unop.hom q}
  map {X Y} f q hq := by
    change D.HarrisRationalLieDeterminantClassCondition C hΦ Y.unop.hom
      (RationalAlgebraAction.pullbackClass f.unop.left q)
    rw [← Over.w f.unop]
    exact D.harrisRationalLieDeterminantClassCondition_baseChange_of_naturality
      C hΦ X.unop.hom f.unop.left (allNaturality X.unop.left) q hq

/-- The actual determinant-compatible moduli presheaf; integral naturality remains explicit. -/
def harrisRationalLieDeterminantPresheaf
    (allNaturality : ∀ X : Scheme.{0}, LieBaseChangeNaturalityStatement X) :
    (Over (Spec (CommRingCat.of (D.kottwitzCocharacterReflexField C))))ᵒᵖ ⥤ Type 1 :=
  (D.harrisRationalLieDeterminantSubfunctor C hΦ allNaturality).toFunctor

/-- Forgetting the determinant condition is a natural inclusion into actual action classes. -/
def harrisRationalLieDeterminantPresheafInclusion
    (allNaturality : ∀ X : Scheme.{0}, LieBaseChangeNaturalityStatement X) :
    D.harrisRationalLieDeterminantPresheaf C hΦ allNaturality ⟶
      RationalAlgebraAction.isoClassOverPresheaf
        (Spec (CommRingCat.of (D.kottwitzCocharacterReflexField C))) A :=
  (D.harrisRationalLieDeterminantSubfunctor C hΦ allNaturality).ι

@[simp]
theorem harrisRationalLieDeterminantPresheaf_obj
    (allNaturality : ∀ X : Scheme.{0}, LieBaseChangeNaturalityStatement X)
    (X : Over (Spec (CommRingCat.of (D.kottwitzCocharacterReflexField C)))) :
    (D.harrisRationalLieDeterminantPresheaf C hΦ allNaturality).obj (op X) =
      D.HarrisRationalLieDeterminantClass C hΦ X.hom := rfl

@[simp]
theorem harrisRationalLieDeterminantPresheaf_map_val
    (allNaturality : ∀ X : Scheme.{0}, LieBaseChangeNaturalityStatement X)
    {X Y : Over (Spec (CommRingCat.of (D.kottwitzCocharacterReflexField C)))}
    (f : Y ⟶ X) (q : D.HarrisRationalLieDeterminantClass C hΦ X.hom) :
    ((D.harrisRationalLieDeterminantPresheaf C hΦ allNaturality).map f.op q).val =
      RationalAlgebraAction.pullbackClass f.left q.val := rfl

@[simp]
theorem harrisRationalLieDeterminantPresheaf_map_classOf_val
    (allNaturality : ∀ X : Scheme.{0}, LieBaseChangeNaturalityStatement X)
    {X Y : Over (Spec (CommRingCat.of (D.kottwitzCocharacterReflexField C)))}
    (f : Y ⟶ X) (Z : RationalAlgebraAction X.left A)
    (hZ : D.HarrisRationalLieDeterminantCondition C hΦ X.hom Z.abelianScheme Z.action) :
    ((D.harrisRationalLieDeterminantPresheaf C hΦ allNaturality).map f.op
      (D.harrisRationalLieDeterminantClassOf C hΦ X.hom Z hZ)).val =
        RationalAlgebraAction.classOf ((RationalAlgebraAction.pullback f.left).obj Z) := rfl

theorem harrisRationalLieDeterminantPresheafInclusion_injective
    (allNaturality : ∀ X : Scheme.{0}, LieBaseChangeNaturalityStatement X)
    (X : Over (Spec (CommRingCat.of (D.kottwitzCocharacterReflexField C)))) :
    Function.Injective
      ((D.harrisRationalLieDeterminantPresheafInclusion C hΦ allNaturality).app (op X)) :=
  Subtype.val_injective

end Langlands.Shimura.CentralSimpleUnitaryData
