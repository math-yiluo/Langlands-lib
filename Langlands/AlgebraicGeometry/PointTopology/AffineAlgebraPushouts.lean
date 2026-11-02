import Langlands.AlgebraicGeometry.PointTopology.Affine
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.Ring.Constructions

/-!
# Tensor pushouts over a specified base algebra
-/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R C A B : Type u)
variable [CommRing R] [CommRing C] [CommRing A] [CommRing B]
variable [Algebra R C] [Algebra R A] [Algebra R B]
variable [Algebra C A] [Algebra C B] [IsScalarTower R C A] [IsScalarTower R C B]

/-- The tensor algebra as a pushout cocone in algebras over the specified base. -/
def affineTensorPushout : PushoutCocone
    (CommAlgCat.ofHom (IsScalarTower.toAlgHom R C A))
    (CommAlgCat.ofHom (IsScalarTower.toAlgHom R C B)) :=
  PushoutCocone.mk
    (CommAlgCat.ofHom
      ((Algebra.TensorProduct.includeLeft : A →ₐ[C] A ⊗[C] B).restrictScalars R))
    (CommAlgCat.ofHom
      ((Algebra.TensorProduct.includeRight : B →ₐ[C] A ⊗[C] B).restrictScalars R))
    (by ext c; exact Algebra.TensorProduct.tmul_one_eq_one_tmul c)

/-- Forgetting the specified base gives a cocone over the same two ring maps. -/
private def ringCoconeOfAffineCocone (c : PushoutCocone
    (CommAlgCat.ofHom (IsScalarTower.toAlgHom R C A))
    (CommAlgCat.ofHom (IsScalarTower.toAlgHom R C B))) :
    PushoutCocone (CommRingCat.ofHom (algebraMap C A))
      (CommRingCat.ofHom (algebraMap C B)) :=
  PushoutCocone.mk (CommRingCat.ofHom c.inl.hom.toRingHom)
    (CommRingCat.ofHom c.inr.hom.toRingHom) (by
      ext x
      exact congrArg (fun f => f.hom x) c.condition)

/-- The full pushout universal property, with the original base retained. -/
def affineTensorPushoutIsColimit : IsColimit (affineTensorPushout R C A B) :=
  PushoutCocone.isColimitAux' _ fun c => by
    let d := ringCoconeOfAffineCocone R C A B c
    let k : CommRingCat.of (A ⊗[C] B) ⟶ CommRingCat.of c.pt :=
      (CommRingCat.pushoutCoconeIsColimit C A B).desc d
    have hk₁ : (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft : A →ₐ[C] A ⊗[C] B).toRingHom) ≫ k =
          CommRingCat.ofHom c.inl.hom.toRingHom :=
      (CommRingCat.pushoutCoconeIsColimit C A B).fac d WalkingSpan.left
    have hk₂ : (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[C] A ⊗[C] B).toRingHom) ≫ k =
          CommRingCat.ofHom c.inr.hom.toRingHom :=
      (CommRingCat.pushoutCoconeIsColimit C A B).fac d WalkingSpan.right
    let h : A ⊗[C] B →ₐ[R] c.pt :=
      { k.hom with
        commutes' r := by
          have hi :
              (Algebra.TensorProduct.includeLeft : A →ₐ[C] A ⊗[C] B)
                (algebraMap R A r) = algebraMap R (A ⊗[C] B) r :=
            ((Algebra.TensorProduct.includeLeft : A →ₐ[C] A ⊗[C] B).restrictScalars R).commutes r
          rw [← hi]
          exact (congrArg (fun f => f.hom (algebraMap R A r)) hk₁).trans
            (c.inl.hom.commutes r) }
    refine ⟨CommAlgCat.ofHom h, ?_, ?_, ?_⟩
    · ext a
      exact congrArg (fun f => f.hom a) hk₁
    · ext b
      exact congrArg (fun f => f.hom b) hk₂
    · intro m hm₁ hm₂
      apply CommAlgCat.hom_ext
      apply AlgHom.coe_ringHom_injective
      have heq : CommRingCat.ofHom m.hom.toRingHom = k := by
        apply PushoutCocone.IsColimit.hom_ext
          (CommRingCat.pushoutCoconeIsColimit C A B)
        · exact (congrArg (fun f => CommRingCat.ofHom f.hom.toRingHom) hm₁).trans hk₁.symm
        · exact (congrArg (fun f => CommRingCat.ofHom f.hom.toRingHom) hm₂).trans hk₂.symm
      exact congrArg (fun f => f.hom) heq

end Langlands.AlgebraicGeometry.PointTopology
