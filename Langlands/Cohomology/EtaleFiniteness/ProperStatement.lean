import Langlands.Geometry.EtalePullback
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.FieldTheory.IsSepClosed

/-!
# Étale cohomology finiteness for proper schemes

SGA 4 XIV, Corollaire 1.2, for finite locally constant coefficient sheaves.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.Geometry

universe u

set_option autoImplicit false

namespace Langlands.Cohomology

/-- An étale cover by objects on which the module sheaf is constant with a
finite value. The cover is expressed by joint surjectivity on points. -/
def IsFiniteLocallyConstantEtaleSheaf {X : Scheme.{u}} {R : Type u} [CommRing R]
    (T : EtaleDerivedSections.ModuleSheaf X R) : Prop :=
  ∀ x : X, ∃ (U : X.Etale) (M : ModuleCat.{u} R),
    x ∈ Set.range U.hom.base ∧ Finite M ∧
      haveI : Etale U.hom := U.prop
      Nonempty ((EtalePullback.restriction U.hom (ModuleCat.{u} R)).obj T ≅
        (constantSheaf U.left.smallEtaleTopology (ModuleCat.{u} R)).obj M)

/-- The ordinary étale cohomology of a proper scheme over a separably
closed field with finite locally constant module coefficients is finite. -/
def ProperEtaleFinitenessStatement {K : Type u} [Field K] [IsSepClosed K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]
    (R : Type u) [CommRing R] : Prop :=
  ∀ T : EtaleDerivedSections.ModuleSheaf X R,
    IsFiniteLocallyConstantEtaleSheaf T →
    ∀ q : ℕ, Finite ((EtaleDerivedSections.cohomology X R q).obj T)

end Langlands.Cohomology
