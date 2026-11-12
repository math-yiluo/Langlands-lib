import Langlands.AlgebraicGeometry.AlgebraicSpace.ProductPointsGluing

/-! # Algebra equivalences on algebraic-space ring points -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace RingPoints

variable {C : Type u} [CommRing C]
variable (X : AlgebraicSpace (Spec (CommRingCat.of C)))
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra C A] [Algebra C B]

/-- Changing coefficients along an algebra equivalence identifies actual space points. -/
def changeRingEquiv (e : A ≃ₐ[C] B) : RingPoints C X A ≃ RingPoints C X B where
  toFun := changeRing e.toAlgHom
  invFun := changeRing e.symm.toAlgHom
  left_inv x := by
    rw [ProductPointsDescent.changeRing_changeRing]
    have he : e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id C A :=
      AlgHom.ext fun a => e.symm_apply_apply a
    rw [he]
    change X.pullback (PointTopology.ringTestMap C (AlgHom.id C A)) x = x
    rw [PointTopology.ringTestMap_id]
    exact pullback_id X _ x
  right_inv x := by
    rw [ProductPointsDescent.changeRing_changeRing]
    have he : e.toAlgHom.comp e.symm.toAlgHom = AlgHom.id C B :=
      AlgHom.ext fun a => e.apply_symm_apply a
    rw [he]
    change X.pullback (PointTopology.ringTestMap C (AlgHom.id C B)) x = x
    rw [PointTopology.ringTestMap_id]
    exact pullback_id X _ x

@[simp]
theorem changeRingEquiv_apply (e : A ≃ₐ[C] B) (x : RingPoints C X A) :
    changeRingEquiv X e x = changeRing e.toAlgHom x := rfl

@[simp]
theorem changeRingEquiv_symm_apply (e : A ≃ₐ[C] B) (x : RingPoints C X B) :
    (changeRingEquiv X e).symm x = changeRing e.symm.toAlgHom x := rfl

end RingPoints

end Langlands.AlgebraicGeometry.AlgebraicSpace
