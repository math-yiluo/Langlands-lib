/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
import WeilConjectures.AlgebraicGeometry.PinnedBaseChangeMateShifts
import WeilConjectures.AlgebraicGeometry.PinnedSingleTensorShifts

/-! # Shift covariance of the pinned single-complex base-change composite
Source: Stacks Project, Tags 08FE, 08HY, 08IB and 0D5U.
(blueprint: lem-pc-pinned-single-base-change-shift). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false

/-- The source functor of the base-change comparison on single complexes.
Source: Stacks Project, Tag 08HY (blueprint: lem-pc-pinned-single-base-change-shift). -/
def singleDegreeBaseChangeSource
    {X S S' : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S'.toRingedSpace))]
    (f : X ⟶ S) (g : S' ⟶ S) (n : ℤ) :
    X.Modules ⥤ schemeDerivedCategory.{u, w} S' :=
  ((DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n ⋙
    schemeDerivedDirectImage.{u, w, w} f) ⋙ derivedPullback.{u, w} g)

/-- The target functor after applying the single-complex tensor counit.
Source: Stacks Project, Tag 08HY (blueprint: lem-pc-pinned-single-base-change-shift). -/
def singleDegreeBaseChangeTarget
    {X X' S' : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X'.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S'.toRingedSpace))]
    (g' : X' ⟶ X) (f' : X' ⟶ S') (n : ℤ) :
    X.Modules ⥤ schemeDerivedCategory.{u, w} S' :=
  ((Scheme.Modules.tensorPullback g' ⋙ DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) n) ⋙ schemeDerivedDirectImage.{u, w, w} f')

/-- The base-change comparison followed by the composition-pinned tensor counit.
This uses the same composition-pinned left-derived counit as the original comparison.
Source: Stacks Project, Tag 08HY (blueprint: lem-pc-pinned-single-base-change-shift). -/
def singleDegreeBaseChangeComposite
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (h : g' ≫ f = f' ≫ g)
    (n : ℤ) (G : X.Modules) :
    (singleDegreeBaseChangeSource.{u, w} f g n).obj G ⟶
      (singleDegreeBaseChangeTarget.{u, w} g' f' n).obj G :=
  let ε := (Classical.choose
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) g'
  let c : (derivedPullback.{u, w} g').obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj G) ⟶
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) n).obj
          ((Scheme.Modules.tensorPullback g').obj G) :=
    cast (by rfl) (ε.app ((HomotopyCategory.singleFunctor _ n).obj G) ≫
      DerivedCategory.Qh.{w}.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex
          (Scheme.Modules.tensorPullback g') (ComplexShape.up ℤ) n).hom.app G)))
  schemeDerivedBaseChangeMap.{u, w} f f' g g' h
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj G) ≫
    (schemeDerivedDirectImage.{u, w, w} f').map c

theorem pinned_single_base_change_shift
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (h : g' ≫ f = f' ≫ g)
    {D : Type*} [Category D] [HasShift D ℤ]
    (H : schemeDerivedCategory.{u, w} S' ⥤ D) [H.CommShift ℤ] (n : ℤ) :
    ∃ a : singleDegreeBaseChangeSource.{u, w} f g n ⋙ H ≅
        (singleDegreeBaseChangeSource.{u, w} f g 0 ⋙ H) ⋙ shiftFunctor D (-n),
    ∃ b : singleDegreeBaseChangeTarget.{u, w} g' f' n ⋙ H ≅
        (singleDegreeBaseChangeTarget.{u, w} g' f' 0 ⋙ H) ⋙ shiftFunctor D (-n),
    ∀ G : X.Modules,
      H.map (singleDegreeBaseChangeComposite.{u, w} f g g' f' h n G) ≫ b.hom.app G =
        a.hom.app G ≫ (shiftFunctor D (-n)).map
          (H.map (singleDegreeBaseChangeComposite.{u, w} f g g' f' h 0 G)) := by
  set_option backward.defeqAttrib.useBackward true in
    dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
    obtain ⟨s, hs⟩ := exists_pinned_pullback_counit_shifts.{u, w}
    let := s g
    let := s g'
    obtain ⟨τ, hτ, hτshift⟩ :=
      exists_pinned_base_change_mate_shifts.{u, w} s hs f g g' f' h
    have := hτshift
    obtain ⟨c, hc⟩ := exists_pinned_single_tensor_shifts.{u, w} g' (s g') (hs g')
    let F := DerivedCategory.singleFunctors
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let T := (DerivedCategory.singleFunctors
      (SheafOfModules.{u} (moduleRings X'.toRingedSpace))).precomp
        (Scheme.Modules.tensorPullback g')
    let β : F.postcomp (schemeDerivedDirectImage f ⋙ derivedPullback g) ⟶
        T.postcomp (schemeDerivedDirectImage f') :=
      SingleFunctors.postcompNatTrans F τ ≫
        (F.postcompPostcompIso (derivedPullback g') (schemeDerivedDirectImage f')).inv ≫
        SingleFunctors.postcompHom c (schemeDerivedDirectImage f')
    let βH := SingleFunctors.postcompHom β H
    let a := ((F.postcomp (schemeDerivedDirectImage f ⋙ derivedPullback g)).postcomp H).shiftIso
      (-n) n 0 (by omega) |>.symm
    let b := ((T.postcomp (schemeDerivedDirectImage f')).postcomp H).shiftIso
      (-n) n 0 (by omega) |>.symm
    refine ⟨a, b, ?_⟩
    intro G
    have hb := congr_app (βH.comm (-n) n 0 (by omega)) G
    simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hb
    have hβ (i : ℤ) : (βH.hom i).app G =
        H.map (singleDegreeBaseChangeComposite.{u, w} f g g' f' h i G) := by
      change H.map (τ.app ((F.functor i).obj G) ≫ 𝟙 _ ≫
        (schemeDerivedDirectImage f').map ((c.hom i).app G)) = _
      simp only [Category.id_comp]
      rw [hτ, hc]
      rfl
    rw [hβ n, hβ 0] at hb
    apply (cancel_epi
      ((((F.postcomp (schemeDerivedDirectImage f ⋙ derivedPullback g)).postcomp H).shiftIso
        (-n) n 0 (by omega)).hom.app G)).1
    dsimp only [a, b, Iso.symm_hom]
    simp only [Iso.hom_inv_id_app_assoc]
    rw [← Category.assoc, hb, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

end AlgebraicGeometry
