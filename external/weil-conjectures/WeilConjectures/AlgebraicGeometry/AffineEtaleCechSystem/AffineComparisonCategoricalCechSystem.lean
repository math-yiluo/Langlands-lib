/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineComparisonEtaleCechSystem
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.Sites.CechComplex
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.CategoryTheory.Sites.CechComplexFunctor
import WeilConjectures.SixFunctors.ProEtale.Comparison.Continuity
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact

/-! # Categorical finite Čech section systems

Source: Stacks Project, Tag 099U, the two finite Čech limit reductions.
-/

@[expose] public section

universe u' u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.AffineEtaleCechSystem

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

variable {Y : Scheme.{u}} {V : Y.ProEt} {n : ℕ} {U : Fin n → Over V}
  {I : Type u} [SmallCategory I] (S : AffineEtaleCechSystem Y V U I)
  {A : Type u'} [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] (J : Sheaf Y.smallEtaleTopology A)

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- A finite product cocone is colimiting when its components are colimiting and
filtered colimits are exact. Source: Mathlib, HasExactColimitsOfShape and
CategoryTheory.Limits.colim, applied to a finite product diagram. -/
private theorem finiteProductCocone_isColimit
    {K : Type} [Finite K] {D₀ : Type u} [SmallCategory D₀] [IsFiltered D₀]
    [HasColimitsOfShape D₀ A] [HasExactColimitsOfShape D₀ A]
    (D : K → D₀ ⥤ A) (P : D₀ ⥤ A) (π : ∀ k, P ⟶ D k)
    (hP : IsLimit (Fan.mk P π)) (c : ∀ k, Cocone (D k))
    (hc : ∀ k, IsColimit (c k))
    (t : Cocone P) (ρ : ∀ k, t.pt ⟶ (c k).pt)
    (hρ : IsLimit (Fan.mk t.pt ρ))
    (hcompat : ∀ j k, t.ι.app j ≫ ρ k = (π k).app j ≫ (c k).ι.app j) :
    Nonempty (IsColimit t) := by
  let e : Discrete.functor D ⋙ (colim : (D₀ ⥤ A) ⥤ A) ≅
      Discrete.functor (fun k ↦ (c k).pt) :=
    Discrete.natIso fun k ↦ (colimit.isColimit (D k.as)).coconePointUniqueUpToIso (hc k.as)
  let h := (IsLimit.postcomposeHomEquiv e _).symm (isLimitOfPreserves colim hP)
  let eP := h.conePointUniqueUpToIso hρ
  have hm : colimit.desc P t = eP.hom := by
    apply hρ.hom_ext
    intro k
    rw [IsLimit.conePointUniqueUpToIso_hom_comp]
    apply colimit.hom_ext
    intro j
    dsimp [e, Discrete.natIso]
    rw [colimit.ι_desc_assoc, ι_colimMap_assoc]
    erw [IsColimit.comp_coconePointUniqueUpToIso_hom]
    exact hcompat j k.as
  have : IsIso (colimit.desc P t) := hm ▸ inferInstance
  change IsIso ((colimit.isColimit P).desc t) at this
  exact ⟨(colimit.isColimit P).ofPointIso⟩

noncomputable abbrev categoricalStageComplex (i : I) : CochainComplex A ℕ :=
  (cechComplexFunctor (fun b ↦ Over.mk (S.f i b))).obj
    ((Over.forget (S.W i)).op ⋙ J.obj)

noncomputable abbrev categoricalOriginalComplex : CochainComplex A ℕ :=
  (cechComplexFunctor U).obj
    ((Over.forget V).op ⋙ ((comparisonUpperStar A Y).obj J).obj)

@[reassoc]
private lemma cech_d_π {C : Type (u + 1)} [Category.{u} C]
    {W : C} [HasFiniteProducts (Over W)] {m : ℕ} (T : Fin m → Over W)
    (P : Cᵒᵖ ⥤ A) (k : ℕ) (y : Fin (k + 2) → Fin m) :
    ((cechComplexFunctor T).obj ((Over.forget W).op ⋙ P)).d k (k + 1) ≫
        Pi.π (fun z ↦ P.obj (op (Presheaf.cechNerveObj T z).left)) y =
      ∑ l : Fin (k + 2), (-1 : ℤ) ^ l.val •
        (Pi.π (fun z ↦ P.obj (op (Presheaf.cechNerveObj T z).left))
          (y ∘ l.succAbove) ≫ P.map (Presheaf.cechNerveMap T y l.succAbove).left.op) := by
  rw [cechComplexFunctor_obj_d, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro l _
  rw [Preadditive.zsmul_comp]
  congr 1
  erw [Pi.lift_comp_π]
  rfl

private noncomputable def categoricalTransition {i j : I} (a : i ⟶ j) :
    S.categoricalStageComplex J j ⟶ S.categoricalStageComplex J i := by
  refine CochainComplex.ofHom (fun k ↦ Pi.lift fun y ↦
    Pi.π (fun z ↦ J.obj.obj (op (Presheaf.cechNerveObj
      (fun b ↦ Over.mk (S.f j b)) z).left)) y ≫ J.obj.map (S.trans a k y).op) ?_
  intro k
  apply Pi.hom_ext
  intro y
  simp only [Category.assoc, Pi.lift_comp_π]
  erw [cech_d_π, cech_d_π_assoc]
  rw [Preadditive.sum_comp, Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro l _
  simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc]
  erw [Pi.lift_comp_π_assoc]
  simp only [Category.assoc, ← J.obj.map_comp, ← op_comp]
  rw [S.trans_face]

private noncomputable def categoricalDiagram : Iᵒᵖ ⥤ CochainComplex A ℕ where
  obj i := S.categoricalStageComplex J i.unop
  map a := categoricalTransition S J a.unop
  map_id i := by
    ext k : 1
    apply Pi.hom_ext
    intro y
    change Fin (k + 1) → Fin n at y
    dsimp only [categoricalTransition]
    erw [Pi.lift_comp_π]
    simp only [unop_id, S.trans_id, op_id, J.obj.map_id, Category.comp_id,
      HomologicalComplex.id_f, Category.id_comp]
    rfl
  map_comp a b := by
    ext k : 1
    apply Pi.hom_ext
    intro y
    change Fin (k + 1) → Fin n at y
    dsimp only [categoricalTransition, HomologicalComplex.comp_f]
    simp only [Category.assoc]
    erw [Pi.lift_comp_π, Pi.lift_comp_π, Pi.lift_comp_π_assoc]
    simp only [unop_comp, S.trans_comp, op_comp, J.obj.map_comp, Category.assoc]

private noncomputable def categoricalToOriginal (i : I) :
    S.categoricalStageComplex J i ⟶ categoricalOriginalComplex (U := U) J := by
  let F := ((comparisonUpperStar A Y).obj J).obj
  let η := ((comparisonAdjunction A Y).unit.app J).hom
  refine CochainComplex.ofHom (fun k ↦ Pi.lift fun y ↦
    Pi.π (fun z ↦ J.obj.obj (op (Presheaf.cechNerveObj
      (fun b ↦ Over.mk (S.f i b)) z).left)) y ≫
        η.app (op ((S.nerve k y).obj i)) ≫ F.map (S.π k y i).op) ?_
  intro k
  apply Pi.hom_ext
  intro y
  simp only [Category.assoc, Pi.lift_comp_π]
  erw [cech_d_π, cech_d_π_assoc]
  rw [Preadditive.sum_comp, Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro l _
  simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc]
  erw [Pi.lift_comp_π_assoc]
  simp only [Category.assoc]
  congr 2
  rw [← F.map_comp, ← op_comp, S.π_face, op_comp, F.map_comp]
  have hη := η.naturality
    (Presheaf.cechNerveMap (fun b ↦ Over.mk (S.f i b)) y l.succAbove).left.op
  change J.obj.map _ ≫ η.app _ = η.app _ ≫ F.map _ at hη
  rw [← Category.assoc]
  erw [← hη]
  rw [Category.assoc]
  rfl

private noncomputable def categoricalCocone : Cocone (categoricalDiagram S J) where
  pt := categoricalOriginalComplex (U := U) J
  ι.app i := categoricalToOriginal S J i.unop
  ι.naturality i j a := by
    dsimp only [Functor.const_obj_map]
    erw [Category.comp_id]
    change categoricalTransition S J a.unop ≫ categoricalToOriginal S J j.unop =
      categoricalToOriginal S J i.unop
    ext k : 1
    apply Pi.hom_ext
    intro y
    change Fin (k + 1) → Fin n at y
    dsimp only [categoricalTransition, categoricalToOriginal, HomologicalComplex.comp_f]
    simp only [Category.assoc]
    erw [Pi.lift_comp_π, Pi.lift_comp_π, Pi.lift_comp_π_assoc]
    let F := ((comparisonUpperStar A Y).obj J).obj
    let η := ((comparisonAdjunction A Y).unit.app J).hom
    have hη := η.naturality (S.trans a.unop k y).op
    change J.obj.map (S.trans a.unop k y).op ≫ η.app _ =
      η.app _ ≫ F.map ((Scheme.toProEt Y).map (S.trans a.unop k y)).op at hη
    simp only [Category.assoc]
    erw [← Category.assoc (J.obj.map _) (η.app _) _, hη]
    simp only [Category.assoc]
    change _ ≫ η.app _ ≫ F.map _ ≫ F.map _ = _ ≫ η.app _ ≫ F.map _
    erw [← F.map_comp, ← op_comp, S.π_naturality]

private noncomputable def categoricalSectionCocone (k : ℕ) (y : Fin (k + 1) → Fin n) :
    Cocone ((S.nerve k y).op ⋙ J.obj) where
  pt := ((comparisonUpperStar A Y).obj J).obj.obj
    (op (Presheaf.cechNerveObj U y).left)
  ι.app i := ((comparisonAdjunction A Y).unit.app J).hom.app
    (op ((S.nerve k y).obj i.unop)) ≫
      ((comparisonUpperStar A Y).obj J).obj.map (S.π k y i.unop).op
  ι.naturality i j a := by
    dsimp only [Functor.const_obj_map]
    erw [Category.comp_id]
    let F := ((comparisonUpperStar A Y).obj J).obj
    let η := ((comparisonAdjunction A Y).unit.app J).hom
    change J.obj.map (S.trans a.unop k y).op ≫ η.app _ ≫ F.map _ =
      η.app _ ≫ F.map _
    have hη := η.naturality (S.trans a.unop k y).op
    change J.obj.map (S.trans a.unop k y).op ≫ η.app _ =
      η.app _ ≫ F.map ((Scheme.toProEt Y).map (S.trans a.unop k y)).op at hη
    rw [← Category.assoc, hη, Category.assoc, ← F.map_comp, ← op_comp,
      S.π_naturality]

private theorem categoricalSectionIsColimit [IsCofiltered I]
    (hS : ∀ k y, Nonempty (IsLimit
      ((Scheme.ProEt.forget Y ⋙ Over.forget Y).mapCone (S.nerveCone k y))))
    (k : ℕ) (y : Fin (k + 1) → Fin n) :
    Nonempty (IsColimit (categoricalSectionCocone S J k y)) := by
  let F := ((comparisonUpperStar A Y).obj J).obj
  let η := ((comparisonAdjunction A Y).unit.app J).hom
  have : ∀ i, IsAffine ((S.nerve k y).obj i).left := fun i ↦ S.affine i k y
  let hF := (isColimit_comparisonUpperStar_mapCocone_of_isAffine
    A J (S.nerve k y) (S.nerveCone k y) (hS k y).some).some
  have := isIso_comparisonAdjunction_unit A Y
  let e : ((S.nerve k y).op ⋙ J.obj) ≅
      (S.nerve k y).op ⋙ (Scheme.toProEt Y).op ⋙ F :=
    NatIso.ofComponents (fun i ↦ asIso (η.app (op ((S.nerve k y).obj i.unop))))
      (fun a ↦ η.naturality ((S.nerve k y).map a.unop).op)
  exact ⟨(IsColimit.precomposeHomEquiv e _).symm hF⟩

private noncomputable def categoricalDegreeProjection (k : ℕ) (y : Fin (k + 1) → Fin n) :
    categoricalDiagram S J ⋙ HomologicalComplex.eval A (ComplexShape.up ℕ) k ⟶
      (S.nerve k y).op ⋙ J.obj where
  app i := Pi.π (fun z ↦ J.obj.obj (op (Presheaf.cechNerveObj
    (fun b ↦ Over.mk (S.f i.unop b)) z).left)) y
  naturality i j a := by
    change (categoricalTransition S J a.unop).f k ≫ _ = _
    dsimp only [categoricalTransition]
    erw [Pi.lift_comp_π]
    rfl

private theorem categoricalDegreeIsColimit [IsCofiltered I]
    (hS : ∀ k y, Nonempty (IsLimit
      ((Scheme.ProEt.forget Y ⋙ Over.forget Y).mapCone (S.nerveCone k y))))
    (k : ℕ) : Nonempty (IsColimit
      ((HomologicalComplex.eval A (ComplexShape.up ℕ) k).mapCocone
        (categoricalCocone S J))) := by
  let : HasColimitsOfSize.{u, u} A := hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} A
  let : AB5OfSize.{u, u} A := AB5OfSize_of_univLE.{u, u, u + 1, u + 1} A
  let D := fun y : Fin (k + 1) → Fin n ↦ (S.nerve k y).op ⋙ J.obj
  let P := categoricalDiagram S J ⋙ HomologicalComplex.eval A (ComplexShape.up ℕ) k
  let π := categoricalDegreeProjection S J k
  have hP : IsLimit (Fan.mk P π) := by
    apply evaluationJointlyReflectsLimits
    intro i
    exact (isLimitMapConeFanMkEquiv ((evaluation Iᵒᵖ A).obj i) D π).symm
      (productIsProduct _)
  apply finiteProductCocone_isColimit D P π hP
    (categoricalSectionCocone S J k)
    (fun y ↦ (categoricalSectionIsColimit S J hS k y).some)
    _ (fun y ↦ Pi.π _ y) (productIsProduct _)
  intro i y
  change (categoricalToOriginal S J i.unop).f k ≫ Pi.π _ y = _
  dsimp only [categoricalToOriginal, categoricalDegreeProjection,
    categoricalSectionCocone]
  erw [Pi.lift_comp_π]
  rfl

/-- Exactness at a positive degree passes to a degreewise filtered colimit.
Source: Mathlib, CategoryTheory.Limits.colim.exact_mapShortComplex. -/
private theorem exactAt_of_degreewise_colimit
    {D₀ : Type u} [SmallCategory D₀]
    [HasColimitsOfShape D₀ A] [HasExactColimitsOfShape D₀ A]
    (K : D₀ ⥤ CochainComplex A ℕ) (c : Cocone K)
    (hc : ∀ k, IsColimit ((HomologicalComplex.eval A (ComplexShape.up ℕ) k).mapCocone c))
    (q : ℕ) (hK : ∀ i, (K.obj i).ExactAt (q + 1)) : c.pt.ExactAt (q + 1) := by
  let T := (ShortComplex.functorEquivalence D₀ A).inverse.obj
    (K ⋙ HomologicalComplex.shortComplexFunctor' A (ComplexShape.up ℕ) q (q + 1) (q + 2))
  have hT : T.Exact := (ShortComplex.exact_iff_evaluation T).2 fun i ↦
    (HomologicalComplex.exactAt_iff' (K.obj i) q (q + 1) (q + 2)
      (by simp) (by simp)).1 (hK i)
  rw [HomologicalComplex.exactAt_iff' c.pt q (q + 1) (q + 2) (by simp) (by simp)]
  exact colim.exact_mapShortComplex (S := T) hT (hc q) (hc (q + 1)) (hc (q + 2))
    (c.pt.d q (q + 1)) (c.pt.d (q + 1) (q + 2))
    (fun i ↦ (c.ι.app i).comm q (q + 1))
    (fun i ↦ (c.ι.app i).comm (q + 1) (q + 2))

/-- Positive Čech exactness descends along the simultaneous étale presentation.
Source: Stacks Project, Tag 099U, both finite-limit reductions.
(blueprint: stage3-affine-comparison-categorical-cech-system).

Proof: Apply comparison-section continuity to each nerve cone of the simultaneous
presentation. In each degree the indexing set is finite, so exact filtered colimits
commute with the product of these section cocones. Their natural maps commute with
each coface, hence with the alternating differential, and form a cocone of complexes.
The three consecutive degree cocones identify the associated short complex with the
filtered colimit of the stage short complexes. Exactness of filtered colimits then
transports stage exactness in degree q+1 to the original complex. -/
theorem categoricalOriginalExactAt [IsCofiltered I]
    (hS : ∀ k y, Nonempty (IsLimit
      ((Scheme.ProEt.forget Y ⋙ Over.forget Y).mapCone (S.nerveCone k y))))
    (q : ℕ) (hstage : ∀ i, (S.categoricalStageComplex J i).ExactAt (q + 1)) :
    (categoricalOriginalComplex (U := U) J).ExactAt (q + 1) := by
  let : HasColimitsOfSize.{u, u} A := hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} A
  let : AB5OfSize.{u, u} A := AB5OfSize_of_univLE.{u, u, u + 1, u + 1} A
  exact exactAt_of_degreewise_colimit (categoricalDiagram S J) (categoricalCocone S J)
    (fun k ↦ (categoricalDegreeIsColimit S J hS k).some) q (fun i ↦ hstage i.unop)

end AlgebraicGeometry.ProEtale.AffineEtaleCechSystem
