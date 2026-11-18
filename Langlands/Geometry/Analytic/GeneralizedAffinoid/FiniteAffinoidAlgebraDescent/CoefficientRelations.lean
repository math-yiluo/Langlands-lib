import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteTensorComparison.Proof
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Relations of finite coefficient tuples under actual bounded base change -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent

open scoped TensorProduct
open AffinoidPushout

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {A B C D : PresentedAffinoidAlgebra K} {n : ℕ}

/-- Naturality of the actual coefficient sums in a commuting square. -/
theorem coefficientMap_natural (f : BoundedAlgHom K A B) (g : BoundedAlgHom K C D)
    (r : BoundedAlgHom K A C) (p : BoundedAlgHom K B D) (h : p.comp f = g.comp r)
    (b : Fin n → B) (v : Fin n → A) :
    p (f.coefficientMap b v) = g.coefficientMap (fun j => p (b j)) (fun j => r (v j)) := by
  simp only [BoundedAlgHom.coefficientMap_apply]
  change p.toAlgHom (∑ j, f (v j) * b j) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul]
  exact congrArg (fun q : BoundedAlgHom K A D => q (v j) * p (b j)) h

variable (f : BoundedAlgHom K A B) (b : Fin n → B)

/-- The finite coefficient sum viewed as linear over the actual source
algebra through the original structural map. -/
def coefficientLinearMap :
    letI : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
    (Fin n → A) →ₗ[A] B := by
  letI : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  refine { (f.coefficientMap b).toLinearMap.toAddMonoidHom with map_smul' := ?_ }
  intro r v
  change f.coefficientMap b (r • v) = f r * f.coefficientMap b v
  simp only [BoundedAlgHom.coefficientMap_apply, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, mul_assoc]

/-- The source-linear relations of the specified finite tuple. -/
def relations : Submodule A (Fin n → A) :=
  letI : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  LinearMap.ker (coefficientLinearMap f b)

@[simp] theorem mem_relations (v : Fin n → A) : v ∈ relations f b ↔ f.coefficientMap b v = 0 :=
  Iff.rfl

variable [CompleteSpace K]

/-- Under actual bounded base change of a finite Banach algebra, the relations
of a generating tuple are spanned by its coordinatewise restricted relations. -/
theorem relations_pushout (hf : f.IsFiniteBanach) (hb : Function.Surjective (f.coefficientMap b))
    (g : BoundedAlgHom K A C) :
    relations (rightMap f g) (fun j => leftMap f g (b j)) =
      Submodule.span C ((fun a : Fin n → A => fun j => g (a j)) '' (relations f b : Set _)) := by
  let : Algebra A C := g.toAlgHom.toRingHom.toAlgebra
  let : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  let τ : (C ⊗[A] B) →+* AffinoidPushout.algebra f g := tensorComparison f g
  let β := coefficientLinearMap f b
  let E := TensorProduct.piScalarRight A C C (Fin n)
  let γ := (rightMap f g).coefficientMap (fun j => leftMap f g (b j))
  have heval (x : C ⊗[A] (Fin n → A)) : τ (β.baseChange C x) = γ (E x) := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r a =>
      change τ (β.baseChange C (r ⊗ₜ[A] a)) =
        γ (TensorProduct.piScalarRight A C C (Fin n) (r ⊗ₜ[A] a))
      rw [LinearMap.baseChange_tmul, TensorProduct.piScalarRight_apply,
        TensorProduct.piScalarRightHom_tmul]
      change rightMap f g r * leftMap f g (f.coefficientMap b a) =
        (rightMap f g).coefficientMap (fun j => leftMap f g (b j)) (fun j => g (a j) * r)
      simp only [BoundedAlgHom.coefficientMap_apply, map_sum, map_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have h := congrArg (fun q : BoundedAlgHom K A (AffinoidPushout.algebra f g) => q (a j))
        (condition f g)
      change leftMap f g (f (a j)) = rightMap f g (g (a j)) at h
      rw [h]
      ring
  have hexact (x : C ⊗[A] (Fin n → A)) :
      β.baseChange C x = 0 ↔ x ∈ (relations f b).baseChange C :=
    (lTensor_exact C (LinearMap.exact_subtype_ker_map β) hb) x
  have hspan : ((relations f b).baseChange C).map E.toLinearMap =
      Submodule.span C ((fun a : Fin n → A => fun j => g (a j)) '' (relations f b : Set _)) := by
    rw [Submodule.baseChange_eq_span, Submodule.map_span]
    congr 1
    have hcoordinate (a : Fin n → A) : E ((1 : C) ⊗ₜ[A] a) = fun j => g (a j) := by
      change TensorProduct.piScalarRight A C C (Fin n) ((1 : C) ⊗ₜ[A] a) = _
      rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
      exact funext fun j => mul_one (g (a j))
    ext v
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, (hcoordinate a).symm⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨(1 : C) ⊗ₜ[A] a, ⟨a, ha, rfl⟩, hcoordinate a⟩
  have hinj : Function.Injective τ := (tensorComparison_bijective f g hf).1
  ext v
  obtain ⟨x, rfl⟩ := E.surjective v
  rw [← hspan, mem_relations]
  change γ (E x) = 0 ↔ E x ∈ ((relations f b).baseChange C).map E.toLinearMap
  rw [← heval]
  constructor
  · intro h
    exact ⟨x, (hexact x).1 (hinj (h.trans (map_zero τ).symm)), rfl⟩
  · rintro ⟨y, hy, hxy⟩
    have h : y = x := E.injective hxy
    rw [← h, (hexact y).2 hy, map_zero]

end Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent
