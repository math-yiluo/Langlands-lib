/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.AlgebraicGeometry.DirectImageGlobalSectionsKInjectiveAcyclic
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # Global-sections acyclicity of direct images of K-injective complexes

Source: Stacks Project, Cohomology, Tags 0D5T and 079V.
(blueprint: lem-pc-global-sections-direct-image-kinjective-acyclic).
-/

@[expose] public section

universe u wY wA
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private theorem unit_isIso_comp_of_exact
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (J : HomotopyCategory C (ComplexShape.up ℤ))
    [IsIso (F.rightDerivedFunctorUnit.app J)] :
    IsIso ((F ⋙ G).rightDerivedFunctorUnit.app J) := by
  let β := Functor.rightDerivedFunctorCompUnit F G
  have := Functor.isRightDerivedFunctor_rightDerivedFunctor_comp_of_exact F G
  let δ := (F ⋙ G).rightDerivedFunctor.rightDerivedDesc
    (F ⋙ G).rightDerivedFunctorUnit (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor) β
  have : IsIso δ :=
    (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc (F ⋙ G).rightDerivedFunctor
      (F ⋙ G).rightDerivedFunctorUnit (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
      (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor) β).mp inferInstance
  have hβ : IsIso (β.app J) := by
    dsimp [β, Functor.rightDerivedFunctorCompUnit]
    infer_instance
  have h : (F ⋙ G).rightDerivedFunctorUnit.app J ≫ δ.app (DerivedCategory.Qh.obj J) =
      β.app J := Functor.rightDerived_fac_app _ _ _ _ _ _
  have : IsIso ((F ⋙ G).rightDerivedFunctorUnit.app J ≫
      δ.app (DerivedCategory.Qh.obj J)) := by rw [h]; exact hβ
  exact IsIso.of_isIso_comp_right ((F ⋙ G).rightDerivedFunctorUnit.app J)
    (δ.app (DerivedCategory.Qh.obj J))

/-- The direct image of a K-injective complex is acyclic for global sections followed
by any restriction of scalars. This requires neither flatness nor preservation of
K-injectivity by module direct image.
Source: Stacks Project, Cohomology, Lemma 20.28.2 (Tag 0D5T) and Section 20.28 (Tag 079V).
(blueprint: lem-pc-global-sections-direct-image-kinjective-acyclic).

Proof: The existing direct-image global-sections acyclicity theorem says that the
unit of RΓ(Y,-) is invertible at f_*I. Restriction of scalars along φ is exact
for every ring map. For an additive F and exact G, RF followed by RG is a right
derived functor of F followed by G. Its composite unit at an object where the
F unit is invertible is invertible: the G unit is invertible everywhere and RG
preserves isomorphisms. Right-derived uniqueness supplies an invertible descent
comparison whose unit equation transfers invertibility to the usual unit of
R(F followed by G). Apply this with F = Γ(Y,-) and G = restriction along φ.
No K-injectivity of f_*I is asserted. This also covers empty schemes, zero
coefficient rings, and noninjective φ. -/
theorem isIso_globalSections_restrictScalars_unit_on_directImage_kInjective
    {X Y : Scheme.{u}} {A : CommRingCat.{u}}
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    (f : X ⟶ Y) (φ : A ⟶ Γ(Y, ⊤))
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective] :
    IsIso ((RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙
      ModuleCat.restrictScalars φ.hom).rightDerivedFunctorUnit.app
        (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
  let : HasDerivedCategory
      (ModuleCat.{u} ((moduleRings Y.toRingedSpace).obj.obj (op ⊤))) :=
    HasDerivedCategory.standard _
  let J := ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomotopyCategory
    (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)
  have : IsIso
      ((RingedSpace.globalSectionsFunctor Y.toRingedSpace).rightDerivedFunctorUnit.app J) :=
    isIso_directImage_globalSections_unit_on_kInjective f I
  exact unit_isIso_comp_of_exact (RingedSpace.globalSectionsFunctor Y.toRingedSpace)
    (ModuleCat.restrictScalars φ.hom) J

end AlgebraicGeometry
