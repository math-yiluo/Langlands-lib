import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Transport of fibre-module flatness across a surjective algebra map -/

universe u v w x y

open scoped TensorProduct

namespace Langlands.Algebra

/-- Flatness transports along a surjective algebra map whose specified base
change is bijective. This proposition states the transport and does not prove it. -/
def SurjectiveBaseChangeFlatnessTransportStatement : Prop :=
  ∀ (R : Type u) (A : Type v) (S : Type w) (T : Type x) (M : Type y)
    [CommRing R] [CommRing A] [CommRing S] [CommRing T]
    [Algebra R A] [Algebra R S] [Algebra A S] [Algebra R T]
    [IsScalarTower R A S]
    [AddCommGroup M] [Module A M] [Module S M] [IsScalarTower A S M],
    Function.Surjective (algebraMap A S) →
    Function.Bijective
      (_root_.Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A S) (AlgHom.id R T)) →
    Module.Flat (S ⊗[R] T) ((S ⊗[R] T) ⊗[S] M) →
    Module.Flat (A ⊗[R] T) ((A ⊗[R] T) ⊗[A] M)

end Langlands.Algebra
