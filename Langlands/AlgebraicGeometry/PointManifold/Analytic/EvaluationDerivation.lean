import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # Derivations obtained by differentiating families of algebraic points -/
noncomputable section
namespace Langlands.AlgebraicGeometry.PointManifold.Analytic

section Families
variable {k A B E : Type*} [NontriviallyNormedField k]
    [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    [NormedAddCommGroup E] [NormedSpace k E]

/-- The coefficient algebra acts on the value field through the specified point. -/
@[instance_reducible] def pointAlgebra (p : B →ₐ[k] k) : Algebra B k := p.toRingHom.toAlgebra

/-- Differentiating every regular evaluation of a point family gives an algebraic derivation. -/
def evaluationDerivation (q : E → (B →ₐ[k] k)) (t v : E)
    (h : ∀ b, DifferentiableAt k (fun x => q x b) t) :
    letI := pointAlgebra (q t)
    Derivation k B k := by
  letI := pointAlgebra (q t)
  let D : B →ₗ[k] k := {
    toFun := fun b => fderiv k (fun x => q x b) t v
    map_add' := by
      intro a b
      simp only [map_add]
      rw [fderiv_fun_add (h a) (h b)]
      rfl
    map_smul' := by
      intro r b
      simp only [map_smul]
      rw [fderiv_fun_const_smul (h b) r]
      rfl }
  refine Derivation.mk' D ?_
  intro a b
  change fderiv k (fun x => q x (a * b)) t v = _
  simp only [map_mul]
  rw [fderiv_fun_mul (h a) (h b)]
  rfl

@[simp] theorem evaluationDerivation_apply
    (q : E → (B →ₐ[k] k)) (t v : E)
    (h : ∀ b, DifferentiableAt k (fun x => q x b) t) (b : B) :
    evaluationDerivation q t v h b = fderiv k (fun x => q x b) t v := rfl

/-- Formal unramifiedness kills every point-family tangent that kills the base algebra. -/
theorem evaluationDerivation_eq_zero_of_unramified
    (φ : A →ₐ[k] B) (q : E → (B →ₐ[k] k)) (t v : E)
    (h : ∀ b, DifferentiableAt k (fun x => q x b) t)
    (hφ : φ.toRingHom.FormallyUnramified)
    (hzero : ∀ a, fderiv k (fun x => q x (φ a)) t v = 0) :
    ∀ b, fderiv k (fun x => q x b) t v = 0 := by
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : Algebra B k := pointAlgebra (q t)
  letI : Algebra A k := ((q t).comp φ).toRingHom.toAlgebra
  letI : IsScalarTower A B k := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.FormallyUnramified A B := hφ
  let D := evaluationDerivation q t v h
  let DA : Derivation A B k := Derivation.mk' {
    toFun := D
    map_add' := D.map_add
    map_smul' := by
      intro a b
      change D (algebraMap A B a * b) = a • D b
      rw [D.leibniz]
      have hz : D (algebraMap A B a) = 0 := hzero a
      rw [hz, smul_zero, add_zero]
      rfl
  } D.leibniz
  haveI : Subsingleton (Derivation A B k) :=
    (KaehlerDifferential.linearMapEquivDerivation A B).toEquiv.surjective.subsingleton
  intro b
  exact congrArg (fun d : Derivation A B k => d b) (Subsingleton.elim DA 0)

end Families
end Langlands.AlgebraicGeometry.PointManifold.Analytic
