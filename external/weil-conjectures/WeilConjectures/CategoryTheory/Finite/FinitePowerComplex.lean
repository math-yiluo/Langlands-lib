/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Finite power functors and complexes

Source: Stacks Project, Modules on Sites, Tag 03DB.
(blueprint: lem-pur-finite-power-complex).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
variable {A : Type u} [Category.{v} A]

section
variable [HasFiniteProducts A]

/-- The finite categorical power functor. -/
def finitePowerFunctor (d : ℕ) : A ⥤ A where
  obj M := ∏ᶜ fun _ : Fin d ↦ M
  map f := Limits.Pi.map (fun _ : Fin d ↦ f)
  map_id M := by apply Pi.hom_ext; intro i; simp
  map_comp f g := by apply Pi.hom_ext; intro i; simp

/-- Finite power is the diagonal functor followed by the categorical limit.
Source: Stacks Project, Tag 03DB.
(blueprint: lem-pur-finite-power-complex). -/
def finitePowerFunctorIso (d : ℕ) :
    Functor.const (Discrete (Fin d)) ⋙ lim ≅ finitePowerFunctor (A := A) d :=
  NatIso.ofComponents (fun M ↦ (Pi.isoLimit
    ((Functor.const (Discrete (Fin d))).obj M)).symm) (by
      intro M N f
      apply Pi.hom_ext
      intro i
      simp only [Category.assoc]
      change limMap ((Functor.const (Discrete (Fin d))).map f) ≫
          (Pi.isoLimit ((Functor.const (Discrete (Fin d))).obj N)).inv ≫ Pi.π _ i =
        (Pi.isoLimit ((Functor.const (Discrete (Fin d))).obj M)).inv ≫
          Limits.Pi.map (fun _ : Fin d ↦ f) ≫ Pi.π _ i
      rw [Pi.isoLimit_inv_π, Pi.map_π, ← Category.assoc, Pi.isoLimit_inv_π, limMap_π]
      rfl)

instance (d : ℕ) {I : Type*} [Category* I] [HasLimitsOfShape I A] :
    PreservesLimitsOfShape I (finitePowerFunctor (A := A) d) :=
  preservesLimitsOfShape_of_natIso (finitePowerFunctorIso d)

end

section
variable [Preadditive A] [HasFiniteProducts A]

instance (d : ℕ) : (finitePowerFunctor (A := A) d).Additive where
  map_add := by intros; apply Pi.hom_ext; intro i; simp [finitePowerFunctor]

end

section
variable [Abelian A]

instance (d : ℕ) : PreservesFiniteColimits (finitePowerFunctor (A := A) d) := by
  let : HasFiniteBiproducts A := Abelian.hasFiniteBiproducts
  let : HasExactLimitsOfShape (Discrete (Fin d)) A :=
    hasExactLimitsOfShape_discrete_finite A
  exact preservesFiniteColimits_of_natIso (finitePowerFunctorIso d)

end

section
variable [Abelian A]

def finitePowerComplexMap (d : ℕ) (P : CochainComplex A ℤ) :
    ((finitePowerFunctor d).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ∏ᶜ fun _ : Fin d ↦ P :=
  Pi.lift (fun i ↦
    { f := fun k ↦ Pi.π (fun _ : Fin d ↦ P.X k) i
      comm' := by intro k l h; simp [finitePowerFunctor] })

/-- Mapping a complex by the finite power functor is the finite power of the complex.

Source: Stacks Project, Tag 03DB, finite-product interchange.
(blueprint: lem-pur-finite-power-complex).

Proof: the coordinate projections define a chain map. In every degree its composite
with the product comparison for evaluation is the identity, by product extensionality.
Evaluation preserves products, hence that comparison and the chain map in every degree
are isomorphisms. A chain map whose components are isomorphisms is an isomorphism. -/
def finitePowerComplexIso (d : ℕ) (P : CochainComplex A ℤ) :
    ((finitePowerFunctor d).mapHomologicalComplex (.up ℤ)).obj P ≅
      ∏ᶜ fun _ : Fin d ↦ P := by
  have (k : ℤ) : IsIso ((finitePowerComplexMap d P).f k) := by
    have h : (finitePowerComplexMap d P).f k ≫
        piComparison (HomologicalComplex.eval A (.up ℤ) k) (fun _ : Fin d ↦ P) = 𝟙 _ := by
      apply Pi.hom_ext
      intro i
      simp only [Category.assoc, piComparison_comp_π, Category.id_comp]
      change ((finitePowerComplexMap d P) ≫ Pi.π (fun _ : Fin d ↦ P) i).f k = _
      rw [finitePowerComplexMap, Pi.lift_comp_π]
      rfl
    have : IsIso ((finitePowerComplexMap d P).f k ≫
        piComparison (HomologicalComplex.eval A (.up ℤ) k) (fun _ : Fin d ↦ P)) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (piComparison (HomologicalComplex.eval A (.up ℤ) k) (fun _ : Fin d ↦ P))
  have := HomologicalComplex.Hom.isIso_of_components (finitePowerComplexMap d P)
  exact asIso (finitePowerComplexMap d P)

@[reassoc (attr := simp)]
theorem finitePowerComplexIso_projection (d : ℕ) (P : CochainComplex A ℤ)
    (i : Fin d) (k : ℤ) :
    ((finitePowerComplexIso d P).hom ≫ Pi.π (fun _ : Fin d ↦ P) i).f k =
      Pi.π (fun _ : Fin d ↦ P.X k) i := by
  change (finitePowerComplexMap d P ≫ _).f k = _
  rw [finitePowerComplexMap, Pi.lift_comp_π]

end

end CategoryTheory
