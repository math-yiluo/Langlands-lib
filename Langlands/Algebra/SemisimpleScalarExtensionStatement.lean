import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Etale.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Semisimple algebras after scalar extension -/

universe uk uK uA

open scoped TensorProduct

namespace Langlands.Algebra

/-- A finite-dimensional semisimple algebra stays semisimple after a separable
algebraic field extension, or after any field extension if its centre is étale. -/
def SemisimpleScalarExtensionStatement : Prop :=
  ∀ (k : Type uk) (K : Type uK) (A : Type uA)
    [Field k] [Field K] [Ring A] [Algebra k K] [Algebra k A]
    [FiniteDimensional k A],
    IsSemisimpleRing A →
      (Algebra.IsSeparable k K ∨ Algebra.Etale k (Subalgebra.center k A)) →
      IsSemisimpleRing (K ⊗[k] A)

end Langlands.Algebra
