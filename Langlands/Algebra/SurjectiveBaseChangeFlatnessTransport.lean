import Langlands.Algebra.SurjectiveBaseChangeFlatnessTransportStatement

/-! # Proof of flatness transport across a surjective map with bijective base change -/

universe u v w x y

open scoped TensorProduct

namespace Langlands.Algebra

private theorem transport (A : Type u) (S : Type v) (C : Type w) (D : Type x) (M : Type y)
    [CommRing A] [CommRing S] [CommRing C] [CommRing D]
    [Algebra A S] [Algebra A C] [Algebra A D] [Algebra S D] [Algebra C D]
    [IsScalarTower A S D] [IsScalarTower A C D]
    [AddCommGroup M] [Module A M] [Module S M] [IsScalarTower A S M]
    (hAS : Function.Surjective (algebraMap A S))
    (hCD : Function.Bijective (algebraMap C D))
    [Module.Flat D (D ⊗[S] M)] :
    Module.Flat C (C ⊗[A] M) := by
  let e := LinearEquiv.ofBijective (Algebra.linearMap C D) hCD
  let : Module.Flat C D := Module.Flat.of_linearEquiv e.symm
  let : Module.Flat C (D ⊗[S] M) := Module.Flat.trans C D _
  let : TensorProduct.CompatibleSMul A S D M :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective D M hAS
  exact Module.Flat.of_linearEquiv
    ((TensorProduct.AlgebraTensorModule.congr e (LinearEquiv.refl A M)).trans
      (TensorProduct.equivOfCompatibleSMul S A C D M))


/-- The specified bijective base change transports the flat fibre module. -/
theorem surjectiveBaseChangeFlatnessTransport :
    SurjectiveBaseChangeFlatnessTransportStatement.{u, v, w, x, y} := by
  intro R A S T M instR instA instS instT algRA algRS algAS algRT towerRAS
    instM modA modS towerASM hAS hmap hflat
  let : Module.Flat (S ⊗[R] T) ((S ⊗[R] T) ⊗[S] M) := hflat
  let f := _root_.Algebra.TensorProduct.map
    (IsScalarTower.toAlgHom R A S) (AlgHom.id R T)
  let : Algebra (A ⊗[R] T) (S ⊗[R] T) := f.toRingHom.toAlgebra
  let : IsScalarTower A (A ⊗[R] T) (S ⊗[R] T) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change algebraMap A (S ⊗[R] T) a = f (algebraMap A (A ⊗[R] T) a)
      simp [f]
  exact transport A S (A ⊗[R] T) (S ⊗[R] T) M hAS hmap

end Langlands.Algebra
