/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-! # Flat telescope presentations and stage maps

Source: Stacks Project, Tags 06YS and 06YJ; concrete model morphisms in the
normalization plan. (blueprint: def-sc-flat-telescope-stage-map).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

local instance (Y : Scheme.{u}) :
    HasColimitsOfShape (Discrete ℕ)
      (CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) := by
  let C := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  have : HasColimitsOfShape (Discrete ℕ) C := inferInstance
  refine ⟨fun F ↦ ?_⟩
  have (n : ℤ) : HasColimit (F ⋙ HomologicalComplex.eval C (.up ℤ) n) :=
    HasColimitsOfShape.has_colimit _
  exact ⟨⟨⟨_, HomologicalComplex.isColimitCoconeOfHasColimitEval F⟩⟩⟩

/-- A concrete sequential telescope of bounded-above flat complexes.
The transition cone is constructed explicitly; no existence witness supplies its data.
Source: Stacks Project, Tag 06YS, telescope construction.
(blueprint: lem-sc-normalized-flat-telescope-comparison). 
(blueprint: def-sc-flat-telescope-stage-map)
-/
def isFlatTelescope (Y : Scheme.{u})
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) : Prop :=
  ∃ (E : ℕ → CochainComplex
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (t : ∀ n : ℕ, E n ⟶ E (n + 1)),
    (∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E n).X i)) ∧
    (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E n).X i)) ∧
    CochainComplex.mappingCone (𝟙 (∐ E) -
      Sigma.desc (fun n : ℕ ↦ t n ≫ Sigma.ι E (n + 1))) = P

/-- Homotopy objects represented by flat telescopes or their translates by one.
This predicate records actual representatives and contains no choice of data.
Source: Stacks Project, Tag 06YJ.
(blueprint: lem-sc-normalized-flat-telescope-comparison). 
(blueprint: def-sc-flat-telescope-stage-map)
-/
def flatTelescopeShiftRepresentative (Y : Scheme.{u})
    (X : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)) : Prop :=
  ∃ P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
    isFlatTelescope Y P ∧
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P = X ∨
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)⟦(1 : ℤ)⟧ = X)

/-- The endomorphism whose cone is the sequential telescope.
Source: Stacks Project, Tag 06YS.
(blueprint: def-sc-flat-telescope-stage-map). -/
noncomputable def flatTelescopeDifferential {Y : Scheme.{u}}
    (E : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (t : ∀ n : ℕ, E n ⟶ E (n + 1)) : (∐ E) ⟶ (∐ E) :=
  𝟙 (∐ E) - Sigma.desc (fun n : ℕ ↦ t n ≫ Sigma.ι E (n + 1))

/-- Maps obtained from maps of bounded-flat towers, allowing an integer translate
and transport along homotopy isomorphisms. The commutative square is a condition
on the explicitly constructed sum map, not unspecified cone-map data.
Source: Stacks Project, Tags 06YS and 06YJ; model-map part of the parent plan.
(blueprint: def-sc-flat-telescope-stage-map). -/
def flatTelescopeStageMap (Y : Scheme.{u})
    {X X' : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)}
    (s : X ⟶ X') : Prop :=
  ∃ (E E' : ℕ → CochainComplex
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (t : ∀ n : ℕ, E n ⟶ E (n + 1))
    (t' : ∀ n : ℕ, E' n ⟶ E' (n + 1))
    (a : ∀ n : ℕ, E n ⟶ E' n),
    (∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E n).X i)) ∧
    (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E n).X i)) ∧
    (∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E' n).X i)) ∧
    (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E' n).X i)) ∧
    ∃ (comm : flatTelescopeDifferential E t ≫ Limits.Sigma.map a =
        Limits.Sigma.map a ≫ flatTelescopeDifferential E' t')
      (k : ℤ)
      (e : ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (CochainComplex.mappingCone (flatTelescopeDifferential E t)))⟦k⟧ ≅ X)
      (e' : ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (CochainComplex.mappingCone (flatTelescopeDifferential E' t')))⟦k⟧ ≅ X'),
      s = e.inv ≫ ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (CochainComplex.mappingCone.map (flatTelescopeDifferential E t)
          (flatTelescopeDifferential E' t') (Limits.Sigma.map a) (Limits.Sigma.map a) comm))⟦k⟧' ≫
        e'.hom

end AlgebraicGeometry
