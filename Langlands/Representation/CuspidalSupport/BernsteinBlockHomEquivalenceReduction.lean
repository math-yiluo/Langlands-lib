import Langlands.Representation.CuspidalSupport.BernsteinBlockCoproducts
import Langlands.Representation.CuspidalSupport.BernsteinInducedProgeneratorStatement
import Langlands.Representation.CuspidalSupport.BernsteinBlockHomEquivalenceStatement

/-! # The categorical step in Renard VI.10.2

The representation-theoretic VI.10.1 statement is retained as a premise.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

section Construction

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance bernsteinBlockModuleEquivalenceAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance bernsteinBlockModuleEquivalenceTopology :
    TopologicalSpace (rationalPoints G) := pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)
  (s : BernsteinInertialClass.{uF, max uF uV} i ν family)

/-- The actual module-category equivalence supplied by a finitely generated
projective generator of the published Bernstein block. -/
def bernsteinSaturatedBlockModuleEquivalence
    (P : BernsteinSaturatedBlock i ν family s)
    (hproj : ∀ (Y Z : BernsteinSaturatedBlock i ν family s) (q : Y ⟶ Z),
      Epi q → ∀ f : P ⟶ Z, ∃ g : P ⟶ Y, g ≫ q = f)
    (hfinite : Module.Finite (MonoidAlgebra ℂ (rationalPoints G))
      P.obj.representation.asModule)
    (hgen : ∀ (X Y : BernsteinSaturatedBlock i ν family s) (f g : X ⟶ Y),
      f ≠ g → ∃ h : P ⟶ X, h ≫ f ≠ h ≫ g) :
    BernsteinSaturatedBlock i ν family s ≌ ModuleCat.{max uF uV} (End P)ᵐᵒᵖ := by
  let := bernsteinSaturatedBlock_homEquivalence_of_finite_projective_generator
    i ν family s P hproj hfinite hgen
  exact (preadditiveCoyonedaObj P).asEquivalence

/-- The forward functor of the constructed equivalence is exactly the
published module-valued Hom functor. -/
theorem bernsteinSaturatedBlockModuleEquivalence_functor
    (P : BernsteinSaturatedBlock i ν family s)
    (hproj : ∀ (Y Z : BernsteinSaturatedBlock i ν family s) (q : Y ⟶ Z),
      Epi q → ∀ f : P ⟶ Z, ∃ g : P ⟶ Y, g ≫ q = f)
    (hfinite : Module.Finite (MonoidAlgebra ℂ (rationalPoints G))
      P.obj.representation.asModule)
    (hgen : ∀ (X Y : BernsteinSaturatedBlock i ν family s) (f g : X ⟶ Y),
      f ≠ g → ∃ h : P ⟶ X, h ≫ f ≠ h ≫ g) :
    (bernsteinSaturatedBlockModuleEquivalence i ν family s P hproj hfinite hgen).functor =
      preadditiveCoyonedaObj P :=
  rfl

end Construction

/-- The exact published VI.10.1 progenerator proposition implies the exact
published VI.10.2 Hom-equivalence proposition, with no further premise. -/
theorem bernsteinBlockHomEquivalence_of_inducedProgenerator
    (hProg : BernsteinInducedProgeneratorStatement.{uF, uV}) :
    BernsteinBlockHomEquivalenceStatement.{uF, uV} := by
  intro F _ _ _ _ G _ _ T i ν _ _ family a ρ₀ hρ₀ j hj
  obtain ⟨hmem, hproj, hfinite, hgen⟩ :=
    hProg F G T i ν family a ρ₀ hρ₀ j hj
  exact ⟨hmem,
    bernsteinSaturatedBlock_homEquivalence_of_finite_projective_generator
      i ν family (bernsteinInertialClass i ν family a) _ hproj hfinite hgen⟩

end Langlands.CuspidalSupport
