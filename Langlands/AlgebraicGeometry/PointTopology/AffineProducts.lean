import Langlands.AlgebraicGeometry.PointTopology.Affine
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Actual affine product-point comparisons

The tensor-product universal property identifies actual algebra-map points with
pairs of points. The scheme-side comparison uses Mathlib's actual scheme pullback
and its isomorphism with the spectrum of the tensor product. Topological product
compatibility is a separate statement and proof unit.
-/

noncomputable section

universe u v w x

open CategoryTheory CategoryTheory.Limits Topology
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.PointTopology

namespace AlgPoint

variable {R : Type u} {A : Type v} {B : Type w} {S : Type x}
variable [CommRing R] [CommRing A] [CommRing B] [CommRing S]
variable [Algebra R A] [Algebra R B] [Algebra R S]

/-- Restriction to the two canonical tensor-product factors. -/
def tensorPointPair (p : AlgPoint R (A ⊗[R] B) S) :
    AlgPoint R A S × AlgPoint R B S :=
  (precomp Algebra.TensorProduct.includeLeft p,
    precomp Algebra.TensorProduct.includeRight p)

@[simp] theorem tensorPointPair_fst_apply (p : AlgPoint R (A ⊗[R] B) S) (a : A) :
    (tensorPointPair p).1 a = p (a ⊗ₜ[R] 1) := rfl

@[simp] theorem tensorPointPair_snd_apply (p : AlgPoint R (A ⊗[R] B) S) (b : B) :
    (tensorPointPair p).2 b = p (1 ⊗ₜ[R] b) := rfl

/-- The actual inverse sends a pure tensor to the product of its two point values. -/
def tensorPointLift (pq : AlgPoint R A S × AlgPoint R B S) :
    AlgPoint R (A ⊗[R] B) S :=
  ofAlgHom (Algebra.TensorProduct.productMap pq.1.toAlgHom pq.2.toAlgHom)

@[simp] theorem tensorPointLift_tmul (pq : AlgPoint R A S × AlgPoint R B S)
    (a : A) (b : B) : tensorPointLift pq (a ⊗ₜ[R] b) = pq.1 a * pq.2 b := rfl

/-- Tensor-product points and pairs of actual points are canonically bijective. -/
def tensorPointEquiv : AlgPoint R (A ⊗[R] B) S ≃
    AlgPoint R A S × AlgPoint R B S where
  toFun := tensorPointPair
  invFun := tensorPointLift
  left_inv p := by
    apply algHomEquiv.injective
    apply Algebra.TensorProduct.ext' (S := R)
    intro a b
    change p.toAlgHom (a ⊗ₜ[R] 1) * p.toAlgHom (1 ⊗ₜ[R] b) =
      p.toAlgHom (a ⊗ₜ[R] b)
    rw [← map_mul p.toAlgHom]
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  right_inv pq := by
    apply Prod.ext
    · ext a
      change pq.1 a * pq.2 1 = pq.1 a
      rw [show pq.2 1 = 1 from map_one pq.2.toAlgHom, mul_one]
    · ext b
      change pq.1 1 * pq.2 b = pq.2 b
      rw [show pq.1 1 = 1 from map_one pq.1.toAlgHom, one_mul]

@[simp] theorem tensorPointEquiv_apply (p : AlgPoint R (A ⊗[R] B) S) :
    tensorPointEquiv p = tensorPointPair p := rfl

@[simp] theorem tensorPointEquiv_symm_apply (pq : AlgPoint R A S × AlgPoint R B S) :
    tensorPointEquiv.symm pq = tensorPointLift pq := rfl

theorem continuous_tensorPointPair [TopologicalSpace S] :
    Continuous (tensorPointPair : AlgPoint R (A ⊗[R] B) S →
      AlgPoint R A S × AlgPoint R B S) :=
  (continuous_precomp _).prodMk (continuous_precomp _)

end AlgPoint

section SchemeProducts

open _root_.AlgebraicGeometry

variable (R A B S : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing S]
variable [Algebra R A] [Algebra R B] [Algebra R S]

/-- Actual points over `Spec R` of the scheme-theoretic product of `Spec A` and `Spec B`. -/
def SpecProductPoint :=
  {p : Spec (CommRingCat.of S) ⟶
      pullback (Spec.algebraMap R A) (Spec.algebraMap R B) //
    p ≫ pullback.fst _ _ ≫ Spec.algebraMap R A = Spec.algebraMap R S}

/-- Mathlib's affine pullback isomorphism compares the actual scheme points with
the spectrum-of-tensor-product points, retaining the base equation. -/
def specProductTensorEquiv : SpecProductPoint R A B S ≃ SpecPoint R (A ⊗[R] B) S where
  toFun p := ⟨p.1 ≫ (pullbackSpecIso R A B).hom, by
    change p.1 ≫ (pullbackSpecIso R A B).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (A ⊗[R] B))) = _
    rw [pullbackSpecIso_hom_base]
    exact p.2⟩
  invFun p := ⟨p.1 ≫ (pullbackSpecIso R A B).inv, by
    have hb : (pullbackSpecIso R A B).inv ≫
        pullback.fst (Spec.algebraMap R A) (Spec.algebraMap R B) ≫
          Spec.algebraMap R A = Spec.algebraMap R (A ⊗[R] B) := by
      change (pullbackSpecIso R A B).inv ≫
        pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
          Spec.map (CommRingCat.ofHom (algebraMap R (A ⊗[R] B)))
      rw [← pullbackSpecIso_hom_base, Iso.inv_hom_id_assoc]
    exact (Category.assoc _ _ _).trans ((congrArg (fun f => p.1 ≫ f) hb).trans p.2)⟩
  left_inv p := by
    apply Subtype.ext
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  right_inv p := by
    apply Subtype.ext
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The actual scheme product points, with the affine evaluation topology
transported along Mathlib's pullback comparison. -/
instance [TopologicalSpace S] : TopologicalSpace (SpecProductPoint R A B S) :=
  TopologicalSpace.induced (specProductTensorEquiv R A B S) inferInstance

/-- The scheme pullback comparison is a homeomorphism for the transported topology. -/
def specProductTensorHomeomorph [TopologicalSpace S] :
    SpecProductPoint R A B S ≃ₜ SpecPoint R (A ⊗[R] B) S :=
  (specProductTensorEquiv R A B S).toHomeomorphOfIsInducing ⟨rfl⟩

/-- The actual scheme-product point bijection with the pair of actual factor points. -/
def specProductPointPairEquiv : SpecProductPoint R A B S ≃
    SpecPoint R A S × SpecPoint R B S :=
  (specProductTensorEquiv R A B S).trans <|
    (specPointEquiv R (A ⊗[R] B) S).trans <|
      AlgPoint.tensorPointEquiv.trans <|
        (specPointEquiv R A S).symm.prodCongr (specPointEquiv R B S).symm

end SchemeProducts

end Langlands.AlgebraicGeometry.PointTopology
