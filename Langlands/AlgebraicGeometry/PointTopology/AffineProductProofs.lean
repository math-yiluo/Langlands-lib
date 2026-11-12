import Langlands.AlgebraicGeometry.PointTopology.AffineProductStatements

/-!
# Proofs of the affine product statements

The inverse of tensor-point restriction is continuous: on a pure tensor it is the
product of two coordinate evaluations, and every tensor is a finite sum of pure
tensors. The scheme-side assertions follow by composing the published
homeomorphisms, and by comparing composition with `Spec` of the two tensor
inclusions with Mathlib's pullback projections.
-/

noncomputable section

universe u v w x z

open CategoryTheory CategoryTheory.Limits Topology
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.PointTopology

namespace AlgPoint

section Arithmetic

variable {R : Type u} {A : Type v} {S : Type x}
variable [CommRing R] [CommRing A] [CommRing S] [Algebra R A] [Algebra R S]

theorem apply_zero (p : AlgPoint R A S) : p 0 = 0 := map_zero p.toAlgHom

theorem apply_one (p : AlgPoint R A S) : p 1 = 1 := map_one p.toAlgHom

theorem apply_add (p : AlgPoint R A S) (a b : A) : p (a + b) = p a + p b :=
  map_add p.toAlgHom a b

theorem apply_mul (p : AlgPoint R A S) (a b : A) : p (a * b) = p a * p b :=
  map_mul p.toAlgHom a b

end Arithmetic

section Tensor

variable {R : Type u} {C : Type z} {A : Type v} {B : Type w} {S : Type x}
variable [CommRing R] [CommRing C] [CommRing A] [CommRing B] [CommRing S]
variable [Algebra R C] [Algebra C A] [Algebra C B] [Algebra R A]
variable [IsScalarTower R C A] [Algebra R S]

/-- A map into tensor-coordinate points is continuous once its values at the
factor coordinates `a ⊗ 1` and `1 ⊗ b` are continuous. -/
theorem continuous_of_tmul [TopologicalSpace S] [IsTopologicalRing S]
    {T : Type*} [TopologicalSpace T] (f : T → AlgPoint R (A ⊗[C] B) S)
    (hl : ∀ a : A, Continuous fun t => f t (a ⊗ₜ[C] (1 : B)))
    (hr : ∀ b : B, Continuous fun t => f t ((1 : A) ⊗ₜ[C] b)) : Continuous f := by
  rw [continuous_iff]
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    have h : ∀ t, f t (a ⊗ₜ[C] b) = f t (a ⊗ₜ[C] 1) * f t (1 ⊗ₜ[C] b) := fun t => by
      rw [← apply_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    exact ((hl a).mul (hr b)).congr fun t => (h t).symm
  | add y z hy hz => exact (hy.add hz).congr fun t => (apply_add (f t) y z).symm

end Tensor

section Product

variable {R : Type u} {A : Type v} {B : Type w} {S : Type x}
variable [CommRing R] [CommRing A] [CommRing B] [CommRing S]
variable [Algebra R A] [Algebra R B] [Algebra R S]

theorem continuous_tensorPointLift [TopologicalSpace S] [IsTopologicalRing S] :
    Continuous (tensorPointLift :
      AlgPoint R A S × AlgPoint R B S → AlgPoint R (A ⊗[R] B) S) := by
  apply continuous_of_tmul
  · intro a
    refine ((continuous_eval a).comp continuous_fst).congr fun pq => ?_
    change pq.1 a = pq.1 a * pq.2 1
    rw [apply_one, mul_one]
  · intro b
    refine ((continuous_eval b).comp continuous_snd).congr fun pq => ?_
    change pq.2 b = pq.1 1 * pq.2 b
    rw [apply_one, one_mul]

/-- Restriction to the two tensor factors, as a homeomorphism. -/
def tensorPointHomeomorph [TopologicalSpace S] [IsTopologicalRing S] :
    AlgPoint R (A ⊗[R] B) S ≃ₜ AlgPoint R A S × AlgPoint R B S where
  toEquiv := tensorPointEquiv
  continuous_toFun := continuous_tensorPointPair
  continuous_invFun := continuous_tensorPointLift

@[simp] theorem tensorPointHomeomorph_apply [TopologicalSpace S] [IsTopologicalRing S]
    (p : AlgPoint R (A ⊗[R] B) S) : tensorPointHomeomorph p = tensorPointPair p := rfl

end Product

end AlgPoint

/-- Tensor-point restriction is a homeomorphism, in independent universes. -/
theorem tensorProductTopologyProperty_proof (R : Type u) (A : Type v) (B : Type w)
    (S : Type x) [CommRing R] [CommRing A] [CommRing B] [CommRing S]
    [Algebra R A] [Algebra R B] [Algebra R S] [TopologicalSpace S] [IsTopologicalRing S] :
    TensorProductTopologyProperty R A B S :=
  AlgPoint.tensorPointHomeomorph.isHomeomorph

section SchemeMaps

open _root_.AlgebraicGeometry

variable {R A D S : Type u} [CommRing R] [CommRing A] [CommRing D] [CommRing S]
variable [Algebra R A] [Algebra R D] [Algebra R S]

theorem specMap_algHom_comp_algebraMap (φ : A →ₐ[R] D) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.algebraMap R A =
      Spec.algebraMap R D := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact φ.commutes r

/-- Composition of an actual scheme point with `Spec` of an algebra map. -/
def specPointComap (φ : A →ₐ[R] D) (q : SpecPoint R D S) : SpecPoint R A S :=
  ⟨q.1 ≫ Spec.map (CommRingCat.ofHom φ.toRingHom), by
    rw [Category.assoc, specMap_algHom_comp_algebraMap]
    exact q.2⟩

@[simp] theorem specPointComap_val (φ : A →ₐ[R] D) (q : SpecPoint R D S) :
    (specPointComap φ q).1 = q.1 ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) := rfl

theorem specMap_specPointEquiv (q : SpecPoint R D S) :
    Spec.map (CommRingCat.ofHom (specPointEquiv R D S q).toAlgHom.toRingHom) = q.1 :=
  Spec.map_preimage _

/-- Under the affine point comparison, composition with `Spec φ` is precomposition
with `φ`. -/
theorem specPointEquiv_specPointComap (φ : A →ₐ[R] D) (q : SpecPoint R D S) :
    specPointEquiv R A S (specPointComap φ q) =
      AlgPoint.precomp φ (specPointEquiv R D S q) := by
  have key : CommRingCat.ofHom (specPointEquiv R A S (specPointComap φ q)).toAlgHom.toRingHom =
      CommRingCat.ofHom φ.toRingHom ≫
        CommRingCat.ofHom (specPointEquiv R D S q).toAlgHom.toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp, specMap_specPointEquiv, specMap_specPointEquiv]
    rfl
  ext a
  exact congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of S => f.hom a) key

theorem specPointEquiv_symm_precomp (φ : A →ₐ[R] D) (q : SpecPoint R D S) :
    (specPointEquiv R A S).symm (AlgPoint.precomp φ (specPointEquiv R D S q)) =
      specPointComap φ q := by
  rw [Equiv.symm_apply_eq, specPointEquiv_specPointComap]

end SchemeMaps

section SchemeProducts

open _root_.AlgebraicGeometry

variable (R A B S : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing S]
variable [Algebra R A] [Algebra R B] [Algebra R S]

theorem specProductPointPairEquiv_fst (p : SpecProductPoint R A B S) :
    (specProductPointPairEquiv R A B S p).1 =
      specPointComap (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B)
        (specProductTensorEquiv R A B S p) :=
  specPointEquiv_symm_precomp _ _

theorem specProductPointPairEquiv_snd (p : SpecProductPoint R A B S) :
    (specProductPointPairEquiv R A B S p).2 =
      specPointComap (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B)
        (specProductTensorEquiv R A B S p) :=
  specPointEquiv_symm_precomp _ _

theorem specProductProjection_proof : SpecProductProjectionProperty R A B S := by
  intro p
  constructor
  · rw [specProductPointPairEquiv_fst, specPointComap_val]
    change (p.1 ≫ (pullbackSpecIso R A B).hom) ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B)) = _
    rw [Category.assoc, pullbackSpecIso_hom_fst]
  · rw [specProductPointPairEquiv_snd, specPointComap_val]
    exact (Category.assoc p.1 (pullbackSpecIso R A B).hom _).trans
      (congrArg (fun k => p.1 ≫ k) (pullbackSpecIso_hom_snd R A B))

theorem specProductTopology_proof [TopologicalSpace S] [IsTopologicalRing S] :
    SpecProductTopologyProperty R A B S := by
  let e : SpecProductPoint R A B S ≃ₜ SpecPoint R A S × SpecPoint R B S :=
    (specProductTensorHomeomorph R A B S).trans <|
      (specPointHomeomorph R (A ⊗[R] B) S).trans <|
        AlgPoint.tensorPointHomeomorph.trans <|
          (specPointHomeomorph R A S).symm.prodCongr (specPointHomeomorph R B S).symm
  have he : (e : SpecProductPoint R A B S → SpecPoint R A S × SpecPoint R B S) =
      specProductPointPairEquiv R A B S := rfl
  unfold SpecProductTopologyProperty
  rw [← he]
  exact e.isHomeomorph

/-- Conrad's Proposition 2.1, products: the projection identification and both
product-topology assertions. -/
theorem affineProductProperties_proof [TopologicalSpace S] :
    AffineProductProperties R A B S := by
  refine ⟨specProductProjection_proof R A B S, ?_, ?_⟩
  · intro _
    exact tensorProductTopologyProperty_proof R A B S
  · intro _
    exact specProductTopology_proof R A B S

end SchemeProducts

end Langlands.AlgebraicGeometry.PointTopology
