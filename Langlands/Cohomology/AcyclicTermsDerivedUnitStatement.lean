import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# The actual derived-functor unit on complexes of acyclic terms

This file specifies the comparison; it does not prove it.
-/

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology

universe w w' u v u' v'

/-- The actual bounded-below right-derived-functor unit of a left exact
additive functor is invertible on every bounded-below complex of acyclic
terms, without any restriction on the homology objects. -/
def AcyclicTermsDerivedUnitStatement : Prop :=
  ∀ (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    [EnoughInjectives C]
    (D : Type u') [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex.Plus C),
    (∀ (i : ℤ) (q : ℕ), IsZero ((F.rightDerived (q + 1)).obj (K.obj.X i))) →
    IsIso (F.rightDerivedFunctorPlusUnit.app K)

end Langlands.Cohomology
