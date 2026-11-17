import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Algebra.Opposite

/-! # Galois descent for noncommutative scalar-extended algebras -/

noncomputable section

universe u v w

open scoped TensorProduct

namespace Langlands.GaloisAlgebraDescent

variable (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L]
    (A : Type w) [Ring A] [Algebra K A]

/-- The coefficient action fixes the possibly noncommutative algebra factor. -/
def coefficientConjugate (σ : L ≃ₐ[K] L) : L ⊗[K] A →ₐ[K] L ⊗[K] A :=
  Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A)

@[simp]
theorem coefficientConjugate_tmul (σ : L ≃ₐ[K] L) (l : L) (a : A) :
    coefficientConjugate K L A σ (l ⊗ₜ[K] a) = σ l ⊗ₜ[K] a := rfl

theorem coefficientConjugate_smul (σ : L ≃ₐ[K] L) (l : L) (x : L ⊗[K] A) :
    coefficientConjugate K L A σ (l • x) =
      σ l • coefficientConjugate K L A σ x := by
  induction x using TensorProduct.inductionOn with
  | tmul c a =>
    simp [TensorProduct.smul_tmul', map_mul]
  | add x y hx hy =>
    simp only [smul_add, map_add, hx, hy]

/-- Coordinates in an extended basis transform by the coefficient action. -/
theorem repr_coefficientConjugate {I : Type*} (b : Module.Basis I K A)
    (σ : L ≃ₐ[K] L) (x : L ⊗[K] A) (i : I) :
    (b.baseChange L).repr (coefficientConjugate K L A σ x) i =
      σ ((b.baseChange L).repr x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul c a => simp [Algebra.smul_def]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

/-- Fixed tensors come from the base algebra, with no commutativity hypothesis
on that algebra. -/
theorem mem_range_includeRight_iff [FiniteDimensional K L] [IsGalois K L]
    (x : L ⊗[K] A) :
    x ∈ (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).range ↔
      ∀ σ : L ≃ₐ[K] L, coefficientConjugate K L A σ x = x := by
  classical
  constructor
  · rintro ⟨a, rfl⟩ σ
    simp [Algebra.TensorProduct.includeRight_apply]
  · intro hx
    let b := Module.Free.chooseBasis K A
    let v := (b.baseChange L).repr x
    have hv : ∀ i, v i ∈ Set.range (algebraMap K L) := by
      intro i
      apply (IsGalois.mem_range_algebraMap_iff_fixed _).mpr
      intro σ
      change σ ((b.baseChange L).repr x i) = (b.baseChange L).repr x i
      rw [← repr_coefficientConjugate, hx σ]
    choose c hc using hv
    refine ⟨∑ i ∈ v.support, c i • b i, ?_⟩
    change (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A)
      (∑ i ∈ v.support, c i • b i) = x
    calc
      _ = ∑ i ∈ v.support, v i • (b.baseChange L) i := by
        simp only [map_sum, map_smul]
        apply Finset.sum_congr rfl
        intro i _
        rw [← hc i, Module.Basis.baseChange_apply]
        simp [Algebra.TensorProduct.includeRight_apply, Algebra.smul_def]
      _ = x := by
        simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using
          (b.baseChange L).linearCombination_repr x

/-- The scalar-extension inclusion remains injective after taking opposites. -/
theorem includeRight_op_injective :
    Function.Injective
      (AlgHom.op (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A)) :=
  fun _ _ h => MulOpposite.unop_injective
    (Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective
      (congrArg MulOpposite.unop h))

variable [FiniteDimensional K L] [IsGalois K L]

variable (q : L ⊗[K] A ≃ₐ[L] (L ⊗[K] A)ᵐᵒᵖ)
    (hq : ∀ (σ : L ≃ₐ[K] L) (x : L ⊗[K] A),
      coefficientConjugate K L A σ (q x).unop =
        (q (coefficientConjugate K L A σ x)).unop)

include hq

/-- An equivariant algebra anti-equivalence preserves the original algebra
inside its scalar extension. -/
theorem opposite_mem_range (a : A) :
    q ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) a) ∈
      (AlgHom.op (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A)).range := by
  obtain ⟨b, hb⟩ := (mem_range_includeRight_iff K L A
    (q ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) a)).unop).mpr
      (fun σ => by rw [hq]; simp [Algebra.TensorProduct.includeRight_apply])
  exact ⟨MulOpposite.op b, MulOpposite.unop_injective hb⟩

/-- Descend an equivariant anti-equivalence of scalar-extended algebras. -/
def descendOppositeHom : A →ₐ[K] Aᵐᵒᵖ :=
  let j := AlgHom.op (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A)
  let hj := includeRight_op_injective K L A
  let f := (q.restrictScalars K).toAlgHom.comp Algebra.TensorProduct.includeRight
  (AlgEquiv.ofInjective j hj).symm.toAlgHom.comp
    (f.codRestrict j.range (opposite_mem_range K L A q hq))

/-- Scalar extension recovers the original anti-equivalence on base elements. -/
theorem includeRight_descendOppositeHom (a : A) :
    (AlgHom.op (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A))
      (descendOppositeHom K L A q hq a) =
        q ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) a) := by
  dsimp [descendOppositeHom]
  rw [← AlgEquiv.ofInjective_apply _ (includeRight_op_injective K L A)]
  simp only [AlgEquiv.apply_symm_apply]
  rfl

/-- The descended algebra homomorphism remains injective. -/
theorem descendOppositeHom_injective :
    Function.Injective (descendOppositeHom K L A q hq) := by
  intro a b h
  apply Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective
  apply q.injective
  simpa only [includeRight_descendOppositeHom] using
    congrArg (AlgHom.op
      (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A)) h

/-- Finite-dimensional equivariant anti-equivalences descend to actual
scalar-fixing algebra equivalences with the opposite algebra. -/
def descendOppositeEquiv [FiniteDimensional K A] : A ≃ₐ[K] Aᵐᵒᵖ :=
  AlgEquiv.ofBijective (descendOppositeHom K L A q hq)
    ⟨descendOppositeHom_injective K L A q hq,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (f := (descendOppositeHom K L A q hq).toLinearMap)
        (MulOpposite.opLinearEquiv K : A ≃ₗ[K] Aᵐᵒᵖ).finrank_eq).mp
          (descendOppositeHom_injective K L A q hq)⟩

end Langlands.GaloisAlgebraDescent
