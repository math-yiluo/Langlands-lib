import Langlands.AlgebraicGeometry.PointTopology.Affine
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Tensor points over a varying common point
-/

noncomputable section

universe u v

open Topology
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R C A B : Type u) (S : Type v)
variable [CommRing R] [CommRing C] [CommRing A] [CommRing B] [CommRing S]
variable [Algebra R C] [Algebra R A] [Algebra R B] [Algebra R S]
variable [Algebra C A] [Algebra C B] [IsScalarTower R C A] [IsScalarTower R C B]

/-- Two actual points whose restrictions to the common algebra agree.
There is no chosen algebra structure from `C` to the value ring. -/
def CompatibleAlgPointPair :=
  {pq : AlgPoint R A S × AlgPoint R B S //
    AlgPoint.precomp (IsScalarTower.toAlgHom R C A) pq.1 =
      AlgPoint.precomp (IsScalarTower.toAlgHom R C B) pq.2}

/-- Restriction of an actual tensor point to its two factors. -/
def tensorFiberPointPair (p : AlgPoint R (A ⊗[C] B) S) :
    CompatibleAlgPointPair R C A B S :=
  ⟨(AlgPoint.precomp
      ((Algebra.TensorProduct.includeLeft : A →ₐ[C] A ⊗[C] B).restrictScalars R) p,
    AlgPoint.precomp
      ((Algebra.TensorProduct.includeRight : B →ₐ[C] A ⊗[C] B).restrictScalars R) p),
    by
      apply AlgPoint.ext
      intro c
      exact congrArg p (Algebra.TensorProduct.tmul_one_eq_one_tmul c)⟩

/-- The inverse uses the common point to give the value ring its temporary
`C`-algebra structure, then restricts the tensor lift back to `R`. -/
def tensorFiberPointLift (pq : CompatibleAlgPointPair R C A B S) :
    AlgPoint R (A ⊗[C] B) S := by
  let hC : C →ₐ[R] S :=
    pq.1.1.toAlgHom.comp (IsScalarTower.toAlgHom R C A)
  letI : Algebra C S := hC.toRingHom.toAlgebra
  letI : IsScalarTower R C S := IsScalarTower.of_algHom hC
  let f : A →ₐ[C] S :=
    { pq.1.1.toAlgHom with commutes' c := rfl }
  let g : B →ₐ[C] S :=
    { pq.1.2.toAlgHom with
      commutes' c := by
        exact (congrArg (fun p => p c) pq.2).symm }
  exact AlgPoint.ofAlgHom ((Algebra.TensorProduct.productMap f g).restrictScalars R)

@[simp] theorem tensorFiberPointLift_tmul
    (pq : CompatibleAlgPointPair R C A B S) (a : A) (b : B) :
    tensorFiberPointLift R C A B S pq (a ⊗ₜ[C] b) = pq.1.1 a * pq.1.2 b := rfl

/-- The tensor universal property on actual points, with the common point
allowed to vary through the compatible-pair space. -/
def tensorFiberPointEquiv : AlgPoint R (A ⊗[C] B) S ≃
    CompatibleAlgPointPair R C A B S where
  toFun := tensorFiberPointPair R C A B S
  invFun := tensorFiberPointLift R C A B S
  left_inv p := by
    apply AlgPoint.ext
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
        change p.toAlgHom (a ⊗ₜ[C] 1) * p.toAlgHom (1 ⊗ₜ[C] b) =
          p.toAlgHom (a ⊗ₜ[C] b)
        rw [← map_mul p.toAlgHom]
        simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add t₁ t₂ h₁ h₂ =>
        change (tensorFiberPointLift R C A B S
          (tensorFiberPointPair R C A B S p)).toAlgHom (t₁ + t₂) =
            p.toAlgHom (t₁ + t₂)
        rw [map_add, map_add]
        exact congrArg₂ (· + ·) h₁ h₂
  right_inv pq := by
    apply Subtype.ext
    apply Prod.ext
    · apply AlgPoint.ext
      intro a
      change pq.1.1 a * pq.1.2 1 = pq.1.1 a
      rw [show pq.1.2 1 = 1 from map_one pq.1.2.toAlgHom, mul_one]
    · apply AlgPoint.ext
      intro b
      change pq.1.1 1 * pq.1.2 b = pq.1.2 b
      rw [show pq.1.1 1 = 1 from map_one pq.1.1.toAlgHom, one_mul]

variable [TopologicalSpace S]

/-- The compatible pairs have the subspace topology from the ordinary product. -/
instance : TopologicalSpace (CompatibleAlgPointPair R C A B S) :=
  inferInstanceAs (TopologicalSpace {pq : AlgPoint R A S × AlgPoint R B S //
    AlgPoint.precomp (IsScalarTower.toAlgHom R C A) pq.1 =
      AlgPoint.precomp (IsScalarTower.toAlgHom R C B) pq.2})

theorem continuous_tensorFiberPointPair :
    Continuous (tensorFiberPointPair R C A B S) :=
  ((AlgPoint.continuous_precomp _).prodMk
    (AlgPoint.continuous_precomp _)).subtype_mk _

theorem continuous_tensorFiberPointLift [IsTopologicalRing S] :
    Continuous (tensorFiberPointLift R C A B S) := by
  apply (AlgPoint.continuous_iff _).mpr
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
      change Continuous (fun pq : CompatibleAlgPointPair R C A B S =>
        pq.1.1 a * pq.1.2 b)
      exact ((AlgPoint.continuous_eval a).comp
        (continuous_fst.comp continuous_subtype_val)).fun_mul
        ((AlgPoint.continuous_eval b).comp
          (continuous_snd.comp continuous_subtype_val))
  | add t₁ t₂ h₁ h₂ =>
      have h : (fun pq : CompatibleAlgPointPair R C A B S =>
          tensorFiberPointLift R C A B S pq (t₁ + t₂)) =
          (fun pq => tensorFiberPointLift R C A B S pq t₁ +
            tensorFiberPointLift R C A B S pq t₂) := by
        funext pq
        exact map_add (tensorFiberPointLift R C A B S pq).toAlgHom t₁ t₂
      rw [h]
      exact h₁.fun_add h₂

/-- The actual tensor-point comparison is a homeomorphism for the independent
evaluation and compatible-pair topologies. -/
def tensorFiberPointHomeomorph [IsTopologicalRing S] :
    AlgPoint R (A ⊗[C] B) S ≃ₜ CompatibleAlgPointPair R C A B S where
  toEquiv := tensorFiberPointEquiv R C A B S
  continuous_toFun := continuous_tensorFiberPointPair R C A B S
  continuous_invFun := continuous_tensorFiberPointLift R C A B S

end Langlands.AlgebraicGeometry.PointTopology
