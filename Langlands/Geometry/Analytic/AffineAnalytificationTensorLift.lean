import Langlands.Geometry.Analytic.AffineAnalytificationFibreProductStatement
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Compatible algebra maps out of a relative tensor product -/

noncomputable section

universe u v w x y z

namespace Langlands.Analytic.AffineAnalytification.TensorLiftComparison

open TensorProduct

variable {K : Type u} [CommRing K]
  {C : Type v} [CommRing C] [Algebra K C]
  {A : Type w} [CommRing A] [Algebra K A] [Algebra C A] [IsScalarTower K C A]
  {B : Type x} [CommRing B] [Algebra K B] [Algebra C B] [IsScalarTower K C B]
  {R : Type y} [CommRing R] [Algebra K R]

/-- The two scalar maps into the tensor product agree. -/
theorem include_comp :
    (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[C] B).comp
        (IsScalarTower.toAlgHom K C A) =
      ((Algebra.TensorProduct.includeRight : B →ₐ[C] A ⊗[C] B).restrictScalars K).comp
        (IsScalarTower.toAlgHom K C B) := by
  apply AlgHom.coe_ringHom_injective
  exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap

/-- The tensor-product inclusions jointly determine a K-algebra map, without
requiring a scalar map from C to K. -/
theorem hom_ext {f g : A ⊗[C] B →ₐ[K] R}
    (ha : f.comp (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[C] B) =
      g.comp (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[C] B))
    (hb : f.comp
        ((Algebra.TensorProduct.includeRight : B →ₐ[C] A ⊗[C] B).restrictScalars K) =
      g.comp
        ((Algebra.TensorProduct.includeRight : B →ₐ[C] A ⊗[C] B).restrictScalars K)) :
    f = g := by
  apply AlgHom.coe_ringHom_injective
  apply Algebra.TensorProduct.ringHom_ext
  · exact congrArg (fun h : A →ₐ[K] R => h.toRingHom) ha
  · exact congrArg (fun h : B →ₐ[K] R => h.toRingHom) hb

/-- A compatible pair of K-algebra maps induces the K-algebra map from the
relative tensor product. The temporary C-action is induced by the left map. -/
def lift (a : A →ₐ[K] R) (b : B →ₐ[K] R)
    (hab : a.comp (IsScalarTower.toAlgHom K C A) =
      b.comp (IsScalarTower.toAlgHom K C B)) :
    A ⊗[C] B →ₐ[K] R := by
  letI : Algebra C R := (a.toRingHom.comp (algebraMap C A)).toAlgebra
  let a' : A →ₐ[C] R := { a.toRingHom with commutes' := fun _ => rfl }
  let b' : B →ₐ[C] R :=
    { b.toRingHom with commutes' := fun c => (AlgHom.congr_fun hab c).symm }
  let f : A ⊗[C] B →ₐ[C] R :=
    Algebra.TensorProduct.lift a' b' (fun _ _ => Commute.all _ _)
  exact
    { f.toRingHom with
      commutes' := fun k => by
        change f ((algebraMap K A k) ⊗ₜ[C] (1 : B)) = algebraMap K R k
        change a (algebraMap K A k) * b 1 = algebraMap K R k
        rw [map_one, mul_one, a.commutes] }

@[simp]
theorem lift_tmul (a : A →ₐ[K] R) (b : B →ₐ[K] R)
    (hab : a.comp (IsScalarTower.toAlgHom K C A) =
      b.comp (IsScalarTower.toAlgHom K C B)) (x : A) (y : B) :
    lift a b hab (x ⊗ₜ[C] y) = a x * b y := rfl

@[simp]
theorem lift_comp_includeLeft (a : A →ₐ[K] R) (b : B →ₐ[K] R)
    (hab : a.comp (IsScalarTower.toAlgHom K C A) =
      b.comp (IsScalarTower.toAlgHom K C B)) :
    (lift a b hab).comp (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[C] B) = a := by
  ext x
  change lift a b hab (x ⊗ₜ[C] 1) = a x
  rw [lift_tmul, map_one, mul_one]

@[simp]
theorem lift_comp_includeRight (a : A →ₐ[K] R) (b : B →ₐ[K] R)
    (hab : a.comp (IsScalarTower.toAlgHom K C A) =
      b.comp (IsScalarTower.toAlgHom K C B)) :
    (lift a b hab).comp
        ((Algebra.TensorProduct.includeRight : B →ₐ[C] A ⊗[C] B).restrictScalars K) = b := by
  ext x
  change lift a b hab (1 ⊗ₜ[C] x) = b x
  rw [lift_tmul, map_one, one_mul]

/-- The factorization through the relative tensor product is unique. -/
theorem lift_unique (a : A →ₐ[K] R) (b : B →ₐ[K] R)
    (hab : a.comp (IsScalarTower.toAlgHom K C A) =
      b.comp (IsScalarTower.toAlgHom K C B))
    (f : A ⊗[C] B →ₐ[K] R)
    (ha : f.comp (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[C] B) = a)
    (hb : f.comp
      ((Algebra.TensorProduct.includeRight : B →ₐ[C] A ⊗[C] B).restrictScalars K) = b) :
    f = lift a b hab :=
  hom_ext (ha.trans (lift_comp_includeLeft a b hab).symm)
    (hb.trans (lift_comp_includeRight a b hab).symm)

/-- Postcomposition preserves the tensor lift. In the analytic application the
postcomposition maps are the bounded restrictions between source charts. -/
theorem comp_lift {S : Type z} [CommRing S] [Algebra K S] (r : R →ₐ[K] S)
    (a : A →ₐ[K] R) (b : B →ₐ[K] R)
    (hab : a.comp (IsScalarTower.toAlgHom K C A) =
      b.comp (IsScalarTower.toAlgHom K C B))
    (hab' : (r.comp a).comp (IsScalarTower.toAlgHom K C A) =
      (r.comp b).comp (IsScalarTower.toAlgHom K C B)) :
    r.comp (lift a b hab) = lift (r.comp a) (r.comp b) hab' := by
  apply hom_ext
  · rw [AlgHom.comp_assoc, lift_comp_includeLeft, lift_comp_includeLeft]
  · rw [AlgHom.comp_assoc, lift_comp_includeRight, lift_comp_includeRight]

end Langlands.Analytic.AffineAnalytification.TensorLiftComparison
