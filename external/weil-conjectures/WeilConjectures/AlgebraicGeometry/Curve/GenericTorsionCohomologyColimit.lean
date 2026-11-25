/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTorsion
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import WeilConjectures.AlgebraicGeometry.EtaleSectionsFilteredColimit
import WeilConjectures.AlgebraicGeometry.Curve.EtaleSheafHLargeFilteredColimit

/-!
# Generic direct image and filtered cohomology colimits

We evaluate direct images on the affine etale basis and use continuity of sections
on the qcqs base changes. Continuity of Ext sheaf cohomology then applies to that
image cocone, including diagrams indexed in the coefficient universe.
-/

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme
private theorem lowerStar_isColimit {Y X : Scheme.{u}} (f : Y ⟶ X)
    [QuasiCompact f] [QuasiSeparated f]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    {D : I ⥤ Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cocone D}
    (hc : IsColimit c) :
    Nonempty (IsColimit ((Etale.lowerStar AddCommGrpCat.{u + 1} f).mapCocone c)) := by
  classical
  let R := (AffineEtale.Spec X).sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} (AffineEtale.topology X) X.smallEtaleTopology
  have : R.IsEquivalence :=
    Functor.isEquivalence_of_isOneHypercoverDense.{u} (AffineEtale.Spec X)
      (AffineEtale.topology X) X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let P := sheafToPresheaf (AffineEtale.topology X) AddCommGrpCat.{u + 1}
  refine ⟨isColimitOfReflects R (isColimitOfReflects P ?_)⟩
  apply evaluationJointlyReflectsColimits
  intro V
  let W := (AffineEtale.Spec X).obj V.unop
  have : IsAffine W.left := by
    dsimp [W]
    rw [AffineEtale.Spec_obj_left]
    infer_instance
  have : CompactSpace ((𝟭 Scheme).obj W.left) := inferInstanceAs (CompactSpace W.left)
  have : QuasiSeparatedSpace ((𝟭 Scheme).obj W.left) :=
    inferInstanceAs (QuasiSeparatedSpace W.left)
  let W' := (MorphismProperty.Over.pullback @Etale ⊤ f).obj W
  have : CompactSpace W'.left :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst W.hom f)
  have : QuasiSeparatedSpace W'.left :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst W.hom f)
  -- Transport qcqs section continuity through Ab ≃ Mod(ℤ).
  let J := Y.smallEtaleTopology
  let G := (Functor.asEquivalence
    (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1})).inverse
  have : IsGrothendieckAbelian.{u + 1} (ModuleCat.{u + 1} ℤ) :=
    IsGrothendieckAbelian.of_equivalence
      (Functor.asEquivalence (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1})).symm
  let S := sheafCompose J G
  let E := (sheafSections J (ModuleCat.{u + 1} ℤ)).obj (Opposite.op W')
  let e : Sheaf.composeAndSheafify J G ≅ S :=
    Functor.isoWhiskerLeft S (sheafificationNatIso J (ModuleCat.{u + 1} ℤ)).symm ≪≫
      Functor.rightUnitor S
  have : S.IsLeftAdjoint := Functor.isLeftAdjoint_of_iso e
  have hS : IsColimit (S.mapCocone c) := isColimitOfPreserves S hc
  have hb := etale_sections_filtered_colimit Y ℤ W' I (D ⋙ S) (S.mapCocone c) hS
  have : IsIso (colimit.desc ((D ⋙ S) ⋙ E) (E.mapCocone (S.mapCocone c))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hb
  let hE := ((colimit.isColimit ((D ⋙ S) ⋙ E)).nonempty_isColimit_iff_isIso_desc.mpr
    (inferInstance : IsIso
      (colimit.desc ((D ⋙ S) ⋙ E) (E.mapCocone (S.mapCocone c))))).some
  exact isColimitOfReflects G hE

/-- Generic direct image and etale cohomology preserve the finite-stalk cocone.
Source: blueprint `theorem-cohomology-curves--2`, cohomology passage.
(blueprint: lem-sc-generic-torsion-finite-stalk-colimit-cohomology)
The generic point is affine and qcqs; sections are finite products of invariants, which commute
with the filtered union. The directed-colimit theorem for etale cohomology and the natural
Ext/derived comparison then identify the displayed mapped cocones as colimits.
-/
theorem generic_torsion_cohomology_colimit
    (X : Scheme.{u}) [IsIntegral X] [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Sheaf (Spec X.functionField).smallEtaleTopology AddCommGrpCat.{u + 1})
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    {F : I ⥤ Sheaf (Spec X.functionField).smallEtaleTopology AddCommGrpCat.{u + 1}}
    {ι : F ⟶ (Functor.const I).obj M}
    (hι : Nonempty (IsColimit (Cocone.mk M ι))) :
    ∀ q : ℕ, Nonempty (IsColimit
      (((Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField) ⋙
        Sheaf.functorH X.smallEtaleTopology q).mapCocone (Cocone.mk M ι))) := by
  intro q
  have hc := (lowerStar_isColimit X.fromSpecFunctionField hι.some).some
  exact sheafH_isColimit_large_filtered X hc q
end AlgebraicGeometry.Scheme
