import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Finite generation of the kernel of the canonical tensor retraction -/

universe u v w

open scoped TensorProduct

namespace Langlands.Algebra

/-- Derived supporting statement: if `S` is essentially of finite type over `R`, then the
kernel of the canonical `S`-algebra map `S ⊗[R] T →ₐ[S] T`, `s ⊗ t ↦ algebraMap S T s * t`,
is a finitely generated ideal. This defines the statement only. -/
def TensorRetractionKernelFGStatement : Prop :=
  ∀ (R : Type u) (S : Type v) (T : Type w)
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T],
    Algebra.EssFiniteType R S →
      (RingHom.ker ((AlgHom.liftEquiv R S T T) (AlgHom.id R T))).FG

end Langlands.Algebra
