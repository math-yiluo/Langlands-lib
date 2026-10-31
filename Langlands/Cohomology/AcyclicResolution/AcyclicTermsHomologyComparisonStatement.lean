import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Homology comparison for acyclic terms and acyclic homology

This file defines a proposition; it does not prove the comparison.
The complex is nonnegatively graded and need not be exact.
-/

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology

universe u v u' v'

/-- A left exact additive functor commutes with the homology objects of a
nonnegative complex whose terms and homology objects are all acyclic for
its positive right derived functors. Only existence of isomorphisms is asserted. -/
def AcyclicTermsHomologyComparisonStatement : Prop :=
  ∀ (C : Type u) [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
    (D : Type u') [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex C ℕ),
    (∀ (i r : ℕ), IsZero ((F.rightDerived (r + 1)).obj (K.X i))) →
    (∀ (i r : ℕ), IsZero ((F.rightDerived (r + 1)).obj (K.homology i))) →
    ∀ n : ℕ,
      Nonempty
        ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology n) ≅
          F.obj (K.homology n))

end Langlands.Cohomology
