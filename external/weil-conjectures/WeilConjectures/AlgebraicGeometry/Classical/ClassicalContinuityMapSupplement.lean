/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Proetale.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import WeilConjectures.RingTheory.IndEtaleSmallIndex
import WeilConjectures.RingTheory.ProEtale.Etale
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Limits.FinallySmall
import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.AlgebraicGeometry.ClassicalContinuityMap
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Continuity maps and classical pro-étale sheaves

Source: current blueprint, sec-proetale-coefficients/sk-def-pe-classical-definition,
`sk-def-pe-classical-definition-continuity-map.md`, clauses 1--4 and final paragraph
(blueprint: det-pe-classical-definition-continuity-map).

The index categories and section values live in the common larger universe `u + 1`.
Module coefficients use the intrinsic constant-ring module category of the recorded
small pro-étale site, with the same coefficient lift as `Scheme.proEtaleDerivedCategory`.
-/

@[expose] public section

set_option autoImplicit false

universe u vC uC

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

section Modules

variable {X : Scheme.{u}} (Λ : Type u) [CommRing Λ]

variable (F : ringedSiteModules.{u + 1}
  ((sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1, u} Λ)))))

/-- Sections with scalars restricted along the constant-section sheafification unit.
This is a presheaf of modules over the lifted discrete coefficient ring itself.
Source: current blueprint, continuity-map detail, clause 3
(blueprint: det-pe-classical-definition-continuity-map). -/
noncomputable def moduleSectionPresheaf : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1, u} Λ) := by
  let M := PresheafOfModules.restrictScalarsObj F.val
    (Functor.whiskerRight
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} Λ))))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
  exact
    { obj := M.obj
      map f := M.map f
      map_id U := by ext x; exact congrArg (fun g ↦ g x) (M.map_id U)
      map_comp f g := by ext x; exact congrArg (fun h ↦ h x) (M.map_comp f g) }

/-- The linear continuity map, taking the colimit in coefficient modules.
Its scalar action is restriction along the canonical constant-section maps.
Source: current blueprint, continuity-map detail, clause 3
(blueprint: det-pe-classical-definition-continuity-map). -/
noncomputable def moduleContinuityMap {I : Type (u + 1)} [SmallCategory I]
    [IsCofiltered I] (P : AffinePresentation X I) :
    colimit (sectionDiagram P (moduleSectionPresheaf Λ F)) ⟶
      (moduleSectionPresheaf Λ F).obj (op P.cone.pt) :=
  continuityMap P (moduleSectionPresheaf Λ F)

/-- Classicality of intrinsic constant-ring module sheaves.
Source: current blueprint, continuity-map detail, clause 3
(blueprint: definition-classical-pro-etale-sheaves--1). -/
def IsClassicalModule : Prop :=
  ∀ {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
    (P : AffinePresentation X I), IsIso (moduleContinuityMap Λ F P)

/-- Module classicality agrees with classicality of the underlying set sheaf.
Source: current blueprint, continuity-map detail, clause 3
(blueprint: det-pe-classical-definition-continuity-map).
Proof: filtered module colimits have the corresponding set colimits as underlying sets:
every element comes from a stage and equality is witnessed at a common later stage.
Under this comparison the two continuity maps agree on every coprojection. A linear
map is invertible precisely when its underlying function is bijective. -/
theorem isClassicalModule_iff :
    IsClassicalModule Λ F ↔
      IsClassical ((sheafCompose (Scheme.ProEt.topology X)
        (forget AddCommGrpCat.{u + 1})).obj ((SheafOfModules.toSheaf _).obj F)) := by
  let V := forget (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))
  have h (I : Type (u + 1)) [SmallCategory I] [IsCofiltered I]
      (P : AffinePresentation X I) :
      IsIso (moduleContinuityMap Λ F P) ↔
        Function.Bijective (continuityMap P (moduleSectionPresheaf Λ F ⋙ V)) := by
    rw [← CategoryTheory.isIso_iff_bijective]
    have heq :
        (preservesColimitIso V (sectionDiagram P (moduleSectionPresheaf Λ F))).inv ≫
          V.map (moduleContinuityMap Λ F P) =
            continuityMap P (moduleSectionPresheaf Λ F ⋙ V) := by
      exact preservesColimitIso_inv_comp_desc V
        (sectionDiagram P (moduleSectionPresheaf Λ F))
        (sectionCocone P (moduleSectionPresheaf Λ F))
    rw [← heq, isIso_comp_left_iff]
    exact (isIso_iff_of_reflects_iso _ V).symm
  constructor
  · intro hF I _ _ P
    exact (h I P).mp (hF P)
  · intro hF I _ _ P
    exact (h I P).mpr (hF P)

/-- Classicality of the recorded intrinsic derived category, using its cohomology sheaves.
Source: current blueprint, continuity-map detail, clause 4
(blueprint: definition-classical-pro-etale-sheaves--2). -/
def IsClassicalComplex {X : Scheme.{u}} (Λ : Type u) [CommRing Λ]
    (K : Scheme.proEtaleDerivedCategory X Λ) : Prop :=
  ∀ q : ℤ, IsClassicalModule Λ
    ((@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) q).obj K)

end Modules

end AlgebraicGeometry.ProEtale
