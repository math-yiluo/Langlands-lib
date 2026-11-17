import Langlands.CommutativeAlgebra.StronglyGradedTorsor
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-! # Strong grading from surjectivity of the action graph -/

noncomputable section

universe u v w

open scoped TensorProduct

namespace Langlands.CommutativeAlgebra.StronglyGraded

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M]
variable {c : A →+* AddMonoidAlgebra A M}

/-- Multiplication by a homogeneous element shifts coefficient projections. -/
theorem projection_mul_homogeneous {m : M} {b : A}
    (hb : b ∈ component (c := c) m) (a : A) (n : M) :
    projection (c := c) n (a * b) = projection (c := c) (n - m) a * b := by
  rw [projection_apply, map_mul, hb, AddMonoidAlgebra.coeff_mul_single_apply,
    projection_apply, sub_eq_add_neg]

section Graph

variable {R : Type w} [CommRing R] [Algebra R A]
variable (cR : A →ₐ[R] AddMonoidAlgebra A M)

/-- The coordinate homomorphism of the action graph over the original scalar ring. -/
def graph : A ⊗[R] A →ₐ[A] AddMonoidAlgebra A M :=
  Algebra.TensorProduct.lift AddMonoidAlgebra.singleZeroAlgHom cR
    (fun _ _ => Commute.all _ _)

@[simp] theorem graph_tmul (a b : A) :
    graph cR (a ⊗ₜ[R] b) = AddMonoidAlgebra.single 0 a * cR b := rfl

/-- A coefficient of a simple tensor under the graph map. -/
theorem graph_coeff_tmul (a b : A) (m : M) :
    (graph cR (a ⊗ₜ[R] b)).coeff m =
      a * projection (c := cR.toRingHom) m b := by
  change (AddMonoidAlgebra.single 0 a * cR b).coeff m = a * (cR b).coeff m
  simp only [AddMonoidAlgebra.coeff_single_mul_apply, neg_zero, zero_add]

/-- A surjective graph map supplies all finite homogeneous dual families. -/
theorem strong_of_graph_surjective (hc : IsGrading cR.toRingHom)
    (hgraph : Function.Surjective (graph cR)) : IsStrong (c := cR.toRingHom) := by
  classical
  intro m
  obtain ⟨z, hz⟩ := hgraph (AddMonoidAlgebra.single m 1)
  obtain ⟨n, a, b, rfl⟩ := TensorProduct.exists_sum_tmul_eq z
  have hcoeff : (∑ i, a i * projection (c := cR.toRingHom) m (b i)) = 1 := by
    have h := congrArg (fun z : AddMonoidAlgebra A M => z.coeff m) hz
    simpa only [map_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
      graph_coeff_tmul, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] using h
  have hzero := congrArg (projection (c := cR.toRingHom) 0) hcoeff
  refine ⟨n, (fun i => projection (c := cR.toRingHom) m (b i)),
    (fun i => projection (c := cR.toRingHom) (-m) (a i)),
    (fun i => projection_mem hc m (b i)),
    (fun i => projection_mem hc (-m) (a i)), ?_⟩
  rw [map_sum] at hzero
  simp_rw [projection_mul_homogeneous (projection_mem hc m _), zero_sub] at hzero
  have hone : projection (c := cR.toRingHom) 0 (1 : A) = 1 := by
    change (cR 1).coeff 0 = 1
    rw [map_one]
    simp
  rw [hone] at hzero
  simpa only [mul_comm] using hzero

end Graph

end Langlands.CommutativeAlgebra.StronglyGraded
