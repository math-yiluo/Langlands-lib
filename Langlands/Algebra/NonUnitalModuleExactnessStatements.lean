import Langlands.Algebra.NonUnitalModuleKernels
import Langlands.Algebra.NonUnitalModuleAmbientAbelianProof
import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Exactness in the original category of nonunital modules

This internal derived statement compares Mathlib's categorical exactness with
equality of the published original stable range and kernel. It introduces no
replacement exactness predicate or original-action structure.
-/

set_option autoImplicit false

namespace Langlands.Algebra

open CategoryTheory

universe uA uM

/-- Categorical exactness is equality of the original stable range and kernel. -/
def NonUnitalModuleExactnessStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A]
    (S : ShortComplex (NonUnitalModuleCat.{uA, uM} A)),
    S.Exact ↔ S.f.rangeSubmodule = S.g.kernelSubmodule

/-! Complete proposition interface and both unequal universe specializations. -/

example : Prop := NonUnitalModuleExactnessStatement.{uA, uM}

example : Prop := NonUnitalModuleExactnessStatement.{0, 1}

example : Prop := NonUnitalModuleExactnessStatement.{1, 0}

example :
    NonUnitalModuleExactnessStatement.{uA, uM} =
      (∀ (A : Type uA) [NonUnitalRing A]
        (S : ShortComplex (NonUnitalModuleCat.{uA, uM} A)),
        S.Exact ↔ S.f.rangeSubmodule = S.g.kernelSubmodule) := rfl

end Langlands.Algebra
