/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.Topology.ProfiniteCondensedRing
import WeilConjectures.AlgebraicGeometry.CondensedCoverRestrictionConservative
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat

set_option linter.privateModule false

/-!
# Tor bounds from bounded flat models on a finite pro-etale cover

proof.md, (2) Local models; Stacks Tags 06YQ, 06YY, 07A4, 06YU
(auxiliary; not a blueprint node).

Module objects are identified with sectionwise module sheaves by the existing
`InternalAbelianSheafModule.sectionModuleEquivalence`. Flatness below uses exactly
`SheafOfModules.IsFlatOnSite` on that sectionwise encoding. The derived tensor and Tor
amplitude use the internal-module encoding of the recorded Tor-amplitude dependency.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private noncomputable def transportTensorIso
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F G : C ⥤ D) (e : G ≅ F) (Q N : C) (P M : D)
    (hQ : F.obj Q ≅ P) (hN : F.obj N ≅ M)
    (t : G.obj (Q ⊗ N) ≅ G.obj Q ⊗ G.obj N) :
    F.obj (Q ⊗ N) ≅ P ⊗ M :=
  (e.app _).symm ≪≫ t ≪≫ tensorIso (e.app Q) (e.app N) ≪≫ tensorIso hQ hN

private theorem moduleZeroDescent
    (Γ : Profinite.CondensedRing.{u}) [IsCommMonObj Γ.X] (S : Scheme.{u})
    (𝒰 : Scheme.Cover Scheme.proetalePrecoverage S)
    (H : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Γ.X S))
    (h : ∀ i, IsZero ((CondensedRing.upperStar Γ.X (𝒰.f i)).obj H)) : IsZero H := by
  have hs : IsZero ((DerivedCategory.singleFunctor _ 0).obj H) := by
    apply (condensed_cover_restriction_conservative Γ S 𝒰).2
    intro i
    exact ((DerivedCategory.singleFunctor _ 0).map_isZero (h i)).of_iso
      (((CondensedRing.upperStar Γ.X (𝒰.f i)).mapDerivedCategorySingleFunctor 0).app H)
  exact IsZero.of_full_of_faithful_of_isZero (DerivedCategory.singleFunctor _ 0) H hs

attribute [local irreducible] CondensedRing.upperStar Functor.mapDerivedCategory
  Functor.mapDerivedCategoryHomologyFunctorIso Functor.mapDerivedCategorySingleFunctor
  DerivedCategory.instMonoidalCategory
  CategoryTheory.Mod.monoidalClosed DerivedCategory.monoidalClosed

private theorem coverHomologyZero
    (Γ : Profinite.CondensedRing.{u}) [IsCommMonObj Γ.X] (S : Scheme.{u})
    (𝒰 : Scheme.Cover Scheme.proetalePrecoverage S)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Γ.X S)))
    (q : ℤ)
    (h : ∀ i, IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((CondensedRing.upperStar Γ.X (𝒰.f i)).mapDerivedCategory.obj K))) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj K) := by
  apply moduleZeroDescent Γ S 𝒰
  intro i
  exact (h i).of_iso
    (((CondensedRing.upperStar Γ.X (𝒰.f i)).mapDerivedCategoryHomologyFunctorIso q).app K)

end AlgebraicGeometry.ProEtale
