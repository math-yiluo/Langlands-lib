/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedAmbientAdjoint
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

import WeilConjectures.AlgebraicGeometry.Finite.FiniteCohomologicalDimensionDirectImageCoproducts
import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedAmbientAdjoint
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedSupportTriangle
import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalConstantTensor
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

set_option linter.privateModule false

/-!
# Residue tensor bound for closed support

Source: blueprint theorem-f-shriek-finite-coefficients--1, tensor-support comparison paragraphs
(blueprint: lem-exc-closed-residue-bound).
-/
set_option autoImplicit false
@[expose] public section
universe u
open CategoryTheory Limits MonoidalCategory Pretriangulated
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
private theorem tensor_unit_square
    {C D : Type*} [Category C] [Category D]
    (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
    {L L' : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (adj' : L' ⊣ R)
    (e : L ≅ L')
    (hunit : ∀ V, adj'.unit.app V = adj.unit.app V ≫ R.map (e.hom.app V))
    (μ : (Functor.postcompose₂.obj L).obj TC ≅
      (((Functor.whiskeringLeft₂ _).obj L).obj L).obj TD)
    (K N : C) [IsIso (((adj.rightAdjointProjectionMap μ.hom).app (L.obj K)).app N)] :
    ∃ e₃ : (TC.flip.obj N).obj (R.obj (L'.obj K)) ≅
        R.obj (L'.obj ((TC.obj K).obj N)),
      (TC.flip.obj N).map (adj'.unit.app K) ≫ e₃.hom =
        adj'.unit.app ((TC.obj K).obj N) := by
  let F := TC.flip.obj N
  let H := (TC.obj K).obj N
  let e₃ : F.obj (R.obj (L'.obj K)) ≅ R.obj (L'.obj H) :=
    F.mapIso (R.mapIso (e.app K).symm) ≪≫
      asIso (((adj.rightAdjointProjectionMap μ.hom).app (L.obj K)).app N) ≪≫
      R.mapIso ((μ.app K).app N).symm ≪≫ R.mapIso (e.app H)
  have hcancel : F.map (adj'.unit.app K) ≫ F.map (R.map (e.inv.app K)) =
      F.map (adj.unit.app K) := by
    rw [← F.map_comp, hunit K, Category.assoc, ← R.map_comp,
      e.hom_inv_id_app, R.map_id]
    erw [Category.comp_id]
  have hprojection : F.map (adj.unit.app K) ≫
      (((adj.rightAdjointProjectionMap μ.hom).app (L.obj K)).app N) =
      adj.unit.app H ≫ R.map ((μ.hom.app K).app N) :=
    (Adjunction.unit_app_comp_map_rightAdjointProjectionMap adj μ.hom K N).symm
  refine ⟨e₃, ?_⟩
  dsimp only [e₃, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Iso.app_inv, Iso.app_hom, asIso_hom]
  simp only [← Category.assoc]
  rw [hcancel, hprojection]
  simp only [Category.assoc, ← R.map_comp]
  have hμ : (μ.hom.app K).app N ≫ (μ.inv.app K).app N = 𝟙 _ :=
    ((μ.app K).app N).hom_inv_id
  rw [← Category.assoc, hμ]
  erw [Category.id_comp]
  exact (hunit H).symm

end AlgebraicGeometry.Etale
