/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdmissibleScalarRealizationExact
public import WeilConjectures.AlgebraicGeometry.CartesianCoefficientTwists
public import WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.NumberTheory.Padics.IntegersAlgebra
public import WeilConjectures.NumberTheory.Padics.IntegersFinite
import all WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientModuleEncoding
import WeilConjectures.AlgebraicGeometry.SectionModuleAlgebraicInverseImage
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import all WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare

set_option linter.privateModule false

/-! # Normalized constant-to-integral coefficient pullback

Stacks Tags 093M and 0G7E
(auxiliary; not a blueprint node).

Constant coefficients are represented by their canonical pullback from the point;
constantSchemeIso identifies them with ordinary constant sheaves. All complexes are
integer-indexed and unrestricted. The quotient clause is the pushout description
R tensor_C (C/pi^n) = R/pi^n, including the prescribed quotient projection.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.MonObj
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralCoefficientSquare

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

attribute [local irreducible] Mod.extendScalarsObj Mod.extendScalarsIsoComapInv
attribute [local irreducible] upperStarFromPoint upperStarFromPointComp upperStar
attribute [local irreducible] FiniteConstantModel.scalarToContinuous
set_option backward.isDefEq.respectTransparency.types false

section Comparison
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (g : X ⟶ Y)

end Comparison

private theorem flat_restricted_regular
    (T : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [PreservesFiniteLimits (Mod.extendScalars φ)] :
    SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      ((InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology T)
        R).functor.obj ((Mod.comap φ).obj (Mod.regular S))) := by
  let N := (Mod.comap φ).obj (Mod.regular S)
  have : PreservesFiniteLimits (MonoidalCategory.tensorLeft N ⋙ Mod.forget R) :=
    preservesFiniteLimits_of_natIso (Mod.extendForgetTensorIso φ)
  have : PreservesFiniteLimits (MonoidalCategory.tensorLeft N) :=
    preservesFiniteLimits_of_reflects_of_preserves _ (Mod.forget R)
  exact (InternalAbelianSheafModule.flat_iff_sectionModule
    (Scheme.ProEt.topology T) R N).mp
      ((ObjectProperty.flat_iff_preservesFiniteLimits N).mpr inferInstance)

universe v w

private theorem internal_kflat_iff
    {C : Type w} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    (K : CochainComplex C ℤ) :
    (∀ P : CochainComplex C ℤ, P.Acyclic →
      (CochainComplex.mapBifunctor P K (curriedTensor C)).Acyclic) ↔
    (HomologicalComplex.quasiIso C (.up ℤ)).kFlat K := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff, HomotopyCategory.kFlat_iff_preserves_acyclic]
  constructor
  · intro h Z hZ
    obtain ⟨Z, rfl⟩ := Z.quotient_obj_surjective
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hZ
    have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
      (CochainComplex.mapBifunctor Z K (curriedTensor C))).2 (h Z hZ)
    exact ⟨(HomotopyCategory.subcategoryAcyclic C).prop_of_iso (β_ _ _) hr, hr⟩
  · intro h P hP
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1
      (h _ ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic P).2 hP)).2

end AlgebraicGeometry.ProEtale.IntegralCoefficientSquare
