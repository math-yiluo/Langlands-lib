/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch

import WeilConjectures.AlgebraicGeometry.ProetaleQcqsFpSectionCalculus
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteFinitePresentationInternalHomColimit
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomOver
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteGlobalPresentationInternalHomColimit
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Opposite
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine

/-! Filtered-colimit comparison for abelian pro-etale closed direct image.

## References

* Stacks Project, Tags 0738 (4) and 098D
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem globalSections_preserves_filteredColimits
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I
      (sheafToPresheaf (ProEt.topology X) AddCommGrpCat.{u + 1} ⋙
        (CategoryTheory.evaluation X.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj
          (Opposite.op (ProEt.mk (𝟙 X)))) := by
  have : CompactSpace (ProEt.mk (𝟙 X)).left := inferInstanceAs (CompactSpace X)
  have : QuasiSeparatedSpace (ProEt.mk (𝟙 X)).left :=
    inferInstanceAs (QuasiSeparatedSpace X)
  constructor
  intro F
  have hb := ((AlgebraicGeometry.proetale_qcqs_fp_section_calculus
    X (ProEt.mk (𝟙 X)) I).1 F).1
  have : IsIso (colimit.post F
      (sheafToPresheaf (ProEt.topology X) AddCommGrpCat.{u + 1} ⋙
        (CategoryTheory.evaluation X.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj
          (Opposite.op (ProEt.mk (𝟙 X))))) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hb
  exact preservesColimit_of_isIso_post _ F

set_option backward.isDefEq.respectTransparency false in
private theorem evaluation_preserves_filteredColimits
    (X : Scheme.{u}) (W : X.ProEt) [CompactSpace W.left] [QuasiSeparatedSpace W.left]
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I
      (sheafToPresheaf (ProEt.topology X) AddCommGrpCat.{u + 1} ⋙
        (CategoryTheory.evaluation X.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj (Opposite.op W)) := by
  let M : W.left.ProEt ⥤ X.ProEt :=
    MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale W.hom)
  have : M.IsContinuous (ProEt.topology W.left) (ProEt.topology X) :=
    ProEt.isContinuous_overMap (inferInstance : WeaklyEtale W.hom)
  have : M.IsCocontinuous (ProEt.topology W.left) (ProEt.topology X) :=
    ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale W.hom)
  let L := M.sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} (ProEt.topology W.left) (ProEt.topology X)
  let E := sheafToPresheaf (ProEt.topology W.left) AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation W.left.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj
      (Opposite.op (ProEt.mk (𝟙 W.left)))
  have : PreservesColimitsOfSize.{u + 1, u + 1} L :=
    (M.sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
      (ProEt.topology W.left) (ProEt.topology X)).leftAdjoint_preservesColimits
  have : PreservesColimitsOfShape I E := globalSections_preserves_filteredColimits W.left I
  let e : M.obj (ProEt.mk (𝟙 W.left)) ≅ W :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by exact (Category.id_comp _).symm)
  let h : L ⋙ E ≅
      sheafToPresheaf (ProEt.topology X) AddCommGrpCat.{u + 1} ⋙
        (CategoryTheory.evaluation X.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj (Opposite.op W) :=
    NatIso.ofComponents (fun F ↦ F.obj.mapIso e.op.symm) (by
      intro F G f
      exact (f.hom.naturality e.inv.op).symm)
  exact preservesColimitsOfShape_of_natIso h

set_option backward.isDefEq.respectTransparency false in
/-- Abelian closed direct image commutes with filtered colimits on a qcqs base. -/
theorem proEtale_closed_abelian_filteredColimits {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [CompactSpace X] [QuasiSeparatedSpace X]
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I (proEtaleSheafDirectImage i AddCommGrpCat.{u + 1}) := by
  let R := (AffineProEt.toProEt X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (AffineProEt.topology X) (ProEt.topology X)
  let T := R ⋙ sheafToPresheaf (AffineProEt.topology X) AddCommGrpCat.{u + 1}
  have hT : PreservesColimitsOfShape I T := by
    apply preservesColimitsOfShape_of_evaluation
    intro V
    have : IsAffine (((AffineProEt.toProEt X).obj V.unop).left) :=
      inferInstanceAs (IsAffine V.unop.left)
    exact evaluation_preserves_filteredColimits X ((AffineProEt.toProEt X).obj V.unop) I
  have : ReflectsColimitsOfShape I T := reflectsColimitsOfShape_of_reflectsIsomorphisms
  have : PreservesColimitsOfShape I
      (proEtaleSheafDirectImage i AddCommGrpCat.{u + 1} ⋙ T) := by
    apply preservesColimitsOfShape_of_evaluation
    intro V
    have : IsAffine (((AffineProEt.toProEt X).obj V.unop).left) :=
      inferInstanceAs (IsAffine V.unop.left)
    let W := (proEtaleBaseChange i).obj ((AffineProEt.toProEt X).obj V.unop)
    have : IsAffine W.left := by
      change IsAffine (pullback ((AffineProEt.toProEt X).obj V.unop).hom i)
      have : IsClosedImmersion (pullback.fst V.unop.hom i) := inferInstance
      have : IsAffine V.unop.left := inferInstance
      exact isAffine_of_isAffineHom (Y := V.unop.left) (pullback.fst V.unop.hom i)
    exact evaluation_preserves_filteredColimits Z W I
  exact preservesColimitsOfShape_of_reflects_of_preserves
    (proEtaleSheafDirectImage i AddCommGrpCat.{u + 1}) T

end AlgebraicGeometry.Scheme
