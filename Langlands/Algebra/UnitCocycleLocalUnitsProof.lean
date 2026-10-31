import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
import Langlands.Algebra.UnitCocycleLocalUnitsStatement

/-! # Proof of local unit generators for a unit cocycle along a faithfully flat algebra -/

universe u

open scoped TensorProduct

namespace Langlands.Algebra

open Algebra.TensorProduct (includeLeft includeRight)

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The `R`-linear map `m ↦ u * (m ⊗ 1) - 1 ⊗ m` whose kernel is the descended module of the
unit `u`. -/
noncomputable def unitCocycleDefect (u : S ⊗[R] S) : S →ₗ[R] S ⊗[R] S :=
  LinearMap.mulLeft R u ∘ₗ (includeLeft : S →ₐ[R] S ⊗[R] S).toLinearMap -
    (includeRight : S →ₐ[R] S ⊗[R] S).toLinearMap

lemma unitCocycleDefect_apply (u : S ⊗[R] S) (m : S) :
    unitCocycleDefect u m = u * (m ⊗ₜ[R] (1 : S)) - (1 : S) ⊗ₜ[R] m := rfl

lemma mem_ker_unitCocycleDefect {u : S ⊗[R] S} {m : S} :
    m ∈ LinearMap.ker (unitCocycleDefect u) ↔ u * (m ⊗ₜ[R] (1 : S)) = (1 : S) ⊗ₜ[R] m := by
  rw [LinearMap.mem_ker, unitCocycleDefect_apply, sub_eq_zero]

/-- Base change of the defect map along `S`: on `S ⊗[R] S` it is
`x ↦ u₂₃ * x₁₂ - x₁₃`. -/
lemma lTensor_unitCocycleDefect (u x : S ⊗[R] S) :
    (unitCocycleDefect u).lTensor S x =
      (includeRight : S ⊗[R] S →ₐ[R] S ⊗[R] (S ⊗[R] S)) u *
          Algebra.TensorProduct.map (AlgHom.id R S)
            (includeLeft : S →ₐ[R] S ⊗[R] S) x -
        Algebra.TensorProduct.map (AlgHom.id R S)
          (includeRight : S →ₐ[R] S ⊗[R] S) x := by
  induction x using TensorProduct.inductionOn with
  | tmul s t =>
    simp [unitCocycleDefect_apply, TensorProduct.tmul_sub, Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy =>
    rw [map_add, hx, hy, map_add, map_add, mul_add]
    abel

/-- For a unit `u` of `S ⊗[R] S` satisfying the cocycle identity `u₁₃ = u₂₃ * u₁₂`, with
`R → S` flat, the elements `m` with `u * (m ⊗ 1) = 1 ⊗ m` generate the unit ideal of `S`. -/
lemma span_unitCocycle_eq_top [Module.Flat R S] (u : S ⊗[R] S) (hu : IsUnit u)
    (hc : Algebra.TensorProduct.map (AlgHom.id R S)
        (includeRight : S →ₐ[R] S ⊗[R] S) u =
      (includeRight : S ⊗[R] S →ₐ[R] S ⊗[R] (S ⊗[R] S)) u *
        Algebra.TensorProduct.map (AlgHom.id R S)
          (includeLeft : S →ₐ[R] S ⊗[R] S) u) :
    Ideal.span {m : S | u * (m ⊗ₜ[R] (1 : S)) = (1 : S) ⊗ₜ[R] m} = ⊤ := by
  set N := LinearMap.ker (unitCocycleDefect u)
  have hex := Module.Flat.lTensor_exact S (LinearMap.exact_subtype_ker_map (unitCocycleDefect u))
  have hu0 : (unitCocycleDefect u).lTensor S u = 0 := by
    rw [lTensor_unitCocycleDefect, ← hc, sub_self]
  obtain ⟨y, hy⟩ := (hex u).mp hu0
  have hmem : ∀ z : S ⊗[R] N,
      Algebra.TensorProduct.lmul' R (N.subtype.lTensor S z) ∈
        Ideal.span {m : S | u * (m ⊗ₜ[R] (1 : S)) = (1 : S) ⊗ₜ[R] m} := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul s n =>
      rw [LinearMap.lTensor_tmul, Submodule.subtype_apply,
        Algebra.TensorProduct.lmul'_apply_tmul]
      exact Ideal.mul_mem_left _ s
        (Ideal.subset_span (mem_ker_unitCocycleDefect.mp n.2))
    | add z w hz hw =>
      rw [map_add, map_add]
      exact add_mem hz hw
  have h := hmem y
  rw [hy] at h
  exact Ideal.eq_top_of_isUnit_mem _ h (hu.map _)

/-- The inverse of a unit cocycle is again a cocycle. -/
lemma unitCocycle_inv (u v : S ⊗[R] S) (huv : u * v = 1)
    (hc : Algebra.TensorProduct.map (AlgHom.id R S)
        (includeRight : S →ₐ[R] S ⊗[R] S) u =
      (includeRight : S ⊗[R] S →ₐ[R] S ⊗[R] (S ⊗[R] S)) u *
        Algebra.TensorProduct.map (AlgHom.id R S)
          (includeLeft : S →ₐ[R] S ⊗[R] S) u) :
    Algebra.TensorProduct.map (AlgHom.id R S)
        (includeRight : S →ₐ[R] S ⊗[R] S) v =
      (includeRight : S ⊗[R] S →ₐ[R] S ⊗[R] (S ⊗[R] S)) v *
        Algebra.TensorProduct.map (AlgHom.id R S)
          (includeLeft : S →ₐ[R] S ⊗[R] S) v := by
  set f₁₃ := Algebra.TensorProduct.map (AlgHom.id R S) (includeRight : S →ₐ[R] S ⊗[R] S)
  set f₂₃ := (includeRight : S ⊗[R] S →ₐ[R] S ⊗[R] (S ⊗[R] S))
  set f₁₂ := Algebra.TensorProduct.map (AlgHom.id R S) (includeLeft : S →ₐ[R] S ⊗[R] S)
  have h₁₃ : f₁₃ u * f₁₃ v = 1 := by rw [← map_mul, huv, map_one]
  have h₂₃ : f₂₃ u * f₂₃ v = 1 := by rw [← map_mul, huv, map_one]
  have h₁₂ : f₁₂ u * f₁₂ v = 1 := by rw [← map_mul, huv, map_one]
  linear_combination (-(f₁₃ v) * f₁₂ u * f₁₂ v) * h₂₃ - f₁₃ v * h₁₂ -
    f₂₃ v * f₁₂ v * f₁₃ v * hc + f₂₃ v * f₁₂ v * h₁₃

/-- Proof of `UnitCocycleLocalUnitsStatement`. -/
theorem unitCocycleLocalUnits : UnitCocycleLocalUnitsStatement.{u} := by
  intro R S _ _ _ _ u v huv hc
  have hvu : v * u = 1 := by rw [mul_comm, huv]
  have hMu := span_unitCocycle_eq_top u (IsUnit.of_mul_eq_one v huv) hc
  have hMv := span_unitCocycle_eq_top v (IsUnit.of_mul_eq_one u hvu)
    (unitCocycle_inv u v huv hc)
  set I := Ideal.span {r : R | ∃ m m' : S, u * (m ⊗ₜ[R] (1 : S)) = (1 : S) ⊗ₜ[R] m ∧
      v * (m' ⊗ₜ[R] (1 : S)) = (1 : S) ⊗ₜ[R] m' ∧ algebraMap R S r = m * m'}
  have hmap : I.map (algebraMap R S) = ⊤ := by
    rw [eq_top_iff, ← Ideal.top_mul ⊤]
    nth_rewrite 1 [← hMu]
    rw [← hMv, Ideal.span_mul_span, Ideal.span_le]
    rintro x ⟨m, hm, m', hm', rfl⟩
    have hm₁ : u * (m ⊗ₜ[R] (1 : S)) = (1 : S) ⊗ₜ[R] m := hm
    have hm'₁ : v * (m' ⊗ₜ[R] (1 : S)) = (1 : S) ⊗ₜ[R] m' := hm'
    have heq : (m * m') ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] (m * m') := by
      calc (m * m') ⊗ₜ[R] (1 : S) = (u * v) * ((m ⊗ₜ[R] (1 : S)) * (m' ⊗ₜ[R] (1 : S))) := by
            rw [huv, one_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
        _ = (u * (m ⊗ₜ[R] (1 : S))) * (v * (m' ⊗ₜ[R] (1 : S))) := by ring
        _ = (1 : S) ⊗ₜ[R] (m * m') := by
            rw [hm₁, hm'₁, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    have hrange : m * m' ∈ Set.range (algebraMap R S) := by
      rw [← (Algebra.IsEffective.of_faithfullyFlat R S).eqLocus_includeLeft_includeRight]
      exact heq
    obtain ⟨r, hr⟩ := hrange
    change m * m' ∈ I.map (algebraMap R S)
    rw [← hr]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨m, m', hm₁, hm'₁, hr⟩)
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) I, hmap, Ideal.comap_top]

end Langlands.Algebra
