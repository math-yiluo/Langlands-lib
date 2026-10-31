import Langlands.Algebra.NondegenerateModuleAdditive
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Exactness of the actual inclusion and nondegenerate-part functor

Renard I.1.2, printed pp.7–8/PDF13–14, supplies closure of the actual
full subcategory and exactness of restriction to nondegenerate parts.
This file states the resulting categorical exactness without abelian inputs.
-/

set_option autoImplicit false

namespace Langlands.Algebra

open CategoryTheory

universe uA uM

/-- The actual functors preserve kernels, cokernels and exact short complexes;
the full-subcategory inclusion also reflects exactness. -/
def NondegenerateModuleExactnessStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A),
    (nondegenerateInclusion.{uA, uM} A).PreservesHomology ∧
    (nondegeneratePartFunctor.{uA, uM} hA).PreservesHomology ∧
    (∀ S : ShortComplex (NondegenerateModuleCat.{uA, uM} A),
      (S.map (nondegenerateInclusion A)).Exact ↔ S.Exact) ∧
    (∀ S : ShortComplex (NonUnitalModuleCat.{uA, uM} A),
      S.Exact → (S.map (nondegeneratePartFunctor hA)).Exact)

/-! Complete closed interfaces at arbitrary and unequal universes. -/

example : Prop := NondegenerateModuleExactnessStatement.{uA, uM}

example : NondegenerateModuleExactnessStatement.{uA, uM} =
    (∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A),
      (nondegenerateInclusion.{uA, uM} A).PreservesHomology ∧
      (nondegeneratePartFunctor.{uA, uM} hA).PreservesHomology ∧
      (∀ S : ShortComplex (NondegenerateModuleCat.{uA, uM} A),
        (S.map (nondegenerateInclusion A)).Exact ↔ S.Exact) ∧
      (∀ S : ShortComplex (NonUnitalModuleCat.{uA, uM} A),
        S.Exact → (S.map (nondegeneratePartFunctor hA)).Exact)) := rfl

example : NondegenerateModuleExactnessStatement.{0, 1} =
    (∀ (A : Type) [NonUnitalRing A] (hA : IsIdempotented A),
      (nondegenerateInclusion.{0, 1} A).PreservesHomology ∧
      (nondegeneratePartFunctor.{0, 1} hA).PreservesHomology ∧
      (∀ S : ShortComplex (NondegenerateModuleCat.{0, 1} A),
        (S.map (nondegenerateInclusion A)).Exact ↔ S.Exact) ∧
      (∀ S : ShortComplex (NonUnitalModuleCat.{0, 1} A),
        S.Exact → (S.map (nondegeneratePartFunctor hA)).Exact)) := rfl

example : NondegenerateModuleExactnessStatement.{1, 0} =
    (∀ (A : Type 1) [NonUnitalRing A] (hA : IsIdempotented A),
      (nondegenerateInclusion.{1, 0} A).PreservesHomology ∧
      (nondegeneratePartFunctor.{1, 0} hA).PreservesHomology ∧
      (∀ S : ShortComplex (NondegenerateModuleCat.{1, 0} A),
        (S.map (nondegenerateInclusion A)).Exact ↔ S.Exact) ∧
      (∀ S : ShortComplex (NonUnitalModuleCat.{1, 0} A),
        S.Exact → (S.map (nondegeneratePartFunctor hA)).Exact)) := rfl

end Langlands.Algebra
