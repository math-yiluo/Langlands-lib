import Langlands.AlgebraicGeometry.DvrSmoothening.PointDefect
import Langlands.AlgebraicGeometry.DvrSmoothening.TorsionLength
import Mathlib.RingTheory.Etale.Kaehler

/-! # Invariance of the defect under formally étale maps -/

namespace Langlands.AlgebraicGeometry.DvrSmoothening

open scoped TensorProduct

theorem pointDefect_comp_formallyEtale {R A B R' : Type*} [CommRing R] [CommRing A] [CommRing B]
    [CommRing R'] [Algebra R A] [Algebra R B] [Algebra R R'] [Algebra A B] [IsScalarTower R A B]
    [Algebra.FormallyEtale A B] (φ : B →ₐ[R] R') :
    pointDefect (φ.comp (IsScalarTower.toAlgHom R A B)) = pointDefect φ := by
  let : Algebra B R' := φ.toRingHom.toAlgebra
  let : Algebra A R' := (φ.comp (IsScalarTower.toAlgHom R A B)).toRingHom.toAlgebra
  have : IsScalarTower A B R' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R B R' := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  have : IsScalarTower R A R' := IsScalarTower.of_algebraMap_eq fun x =>
    ((φ.comp (IsScalarTower.toAlgHom R A B)).commutes x).symm
  have h1 : pointDefect φ = torsionLength R' (R' ⊗[B] Ω[B⁄R]) := by
    rfl
  have h2 : pointDefect (φ.comp (IsScalarTower.toAlgHom R A B)) =
      torsionLength R' (R' ⊗[A] Ω[A⁄R]) := by
    rfl
  rw [h1, h2]
  have hbc := KaehlerDifferential.isBaseChange_of_formallyEtale R A B
  let e1 : B ⊗[A] Ω[A⁄R] ≃ₗ[B] Ω[B⁄R] := hbc.equiv
  let e2 : R' ⊗[B] Ω[B⁄R] ≃ₗ[R'] R' ⊗[A] Ω[A⁄R] :=
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R' R') e1.symm).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A B R' R' Ω[A⁄R])
  exact (torsionLength_congr e2).symm

end Langlands.AlgebraicGeometry.DvrSmoothening
