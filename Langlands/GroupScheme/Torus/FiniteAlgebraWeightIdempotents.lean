import Langlands.GroupScheme.SimplyConnected.MatrixNormOneSplitRankUpper

/-! # Weight idempotents of a split torus in a finite algebra unit group -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct Matrix

namespace Langlands.GroupScheme.FiniteAlgebraTorusWeights

open SplitTorusRepresentationWeights FiniteAlgebraUnits
open MatrixNormOneSplitRank (coeffTensor coeffTensor_tmul repr_coeffTensor
  ext_coeffTensor coeffTensor_one_tmul_mul coeffForm coeffForm_apply)

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {K A : Type u} [Field K] [Ring A] [Algebra K A]
  {d : ℕ} {b : Module.Basis (Fin d) K A}
  {I : Type u} [Fintype I] [DecidableEq I]
  (i : splitTorus (Spec (CommRingCat.of K)) I ⟶ groupScheme b)

local notation "R'" => AddMonoidAlgebra K (I → ℤ)
local notation "ρ" => rightRegularRepresentation b

/-- The universal point regarded as a unit of the scalar-extended algebra. -/
def universalUnit : (R' ⊗[K] A)ˣ :=
  affinePointsEquiv b (CommAlgCat.of (CommRingCat.of K) R')
    (splitTorus.universalPoint (R := CommRingCat.of K) I ≫ i.hom.hom)

/-- The coefficient elements `eₘ` of the inverse of the universal unit. -/
def weightElement (m : I → ℤ) : A :=
  coeffTensor (K := K) A m (((universalUnit i)⁻¹ : (R' ⊗[K] A)ˣ) : R' ⊗[K] A)

/-- **Weights act by right multiplication.** The weight matrix `Pₘ` of the
inverse-right-regular representation is the matrix of right multiplication by `eₘ`. -/
theorem weight_mulVec_repr (m : I → ℤ) (x : A) :
    weight ρ I i m *ᵥ ⇑(b.repr x) =
      ⇑(b.repr (x * weightElement i m)) := by
  set Rc := CommAlgCat.of (CommRingCat.of K) R'
  set pt := splitTorus.universalPoint (R := CommRingCat.of K) I
  have h := FiniteAlgebraUnits.affineMatrix_rightRegular_mulVec_repr b Rc
    (pt ≫ i.hom.hom) ((1 : R') ⊗ₜ[K] x)
  have hU : ((MatrixRepresentation.affineMatrix ρ Rc (pt ≫ i.hom.hom) :
      Matrix (Fin d) (Fin d) R')) =
      (universalMatrix ρ I i :
        Matrix (Fin d) (Fin d) R') := by
    rw [MatrixRepresentation.affineMatrix_apply, Category.assoc]
    rfl
  rw [hU] at h
  funext a
  calc (weight ρ I i m *ᵥ ⇑(b.repr x)) a
      = coeffForm m (((universalMatrix ρ I i :
          Matrix (Fin d) (Fin d) R') *ᵥ
            ⇑((b.baseChange R').repr ((1 : R') ⊗ₜ[K] x))) a) := by
        simp only [Matrix.mulVec, dotProduct, map_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Module.Basis.baseChange_repr_tmul, mul_smul_comm, mul_one, map_smul, smul_eq_mul,
          mul_comm]
        rfl
    _ = coeffForm m ((b.baseChange R').repr
          (((1 : R') ⊗ₜ[K] x) * ((universalUnit i)⁻¹ : (R' ⊗[K] A)ˣ)) a) := by
        rw [h]
        rfl
    _ = b.repr (x * weightElement i m) a := by
        rw [coeffForm_apply, ← repr_coeffTensor, coeffTensor_one_tmul_mul]
        rfl

theorem weightElement_eq_zero {m : I → ℤ} (hm : m ∉ weightSupport ρ I i) :
    weightElement i m = 0 := by
  have h := weight_mulVec_repr i m 1
  rw [weight_eq_zero _ _ _ hm, Matrix.zero_mulVec, one_mul] at h
  apply b.repr.injective
  ext a
  simpa using (congrFun h a).symm

theorem repr_weightElement (m : I → ℤ) :
    ⇑(b.repr (weightElement i m)) =
      weight ρ I i m *ᵥ ⇑(b.repr 1) := by
  rw [weight_mulVec_repr, one_mul]

/-- The weight elements are orthogonal idempotents. -/
theorem weightElement_mul (m n : I → ℤ) :
    weightElement i m * weightElement i n = if m = n then weightElement i m else 0 := by
  apply b.repr.injective
  apply DFunLike.coe_injective
  rw [← weight_mulVec_repr, repr_weightElement, Matrix.mulVec_mulVec, weight_mul_weight]
  by_cases h : n = m
  · subst h
    rw [ite_eq_left rfl, ite_eq_left rfl, repr_weightElement]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h), Matrix.zero_mulVec, map_zero,
      Finsupp.coe_zero]

/-- The weight elements add up to `1`. -/
theorem sum_weightElement :
    ∑ m ∈ weightSupport ρ I i, weightElement i m = 1 := by
  apply b.repr.injective
  apply DFunLike.coe_injective
  rw [map_sum, Finsupp.coe_finsetSum, Finset.sum_congr rfl fun m _ => repr_weightElement i m,
    ← Matrix.sum_mulVec, sum_weight, Matrix.one_mulVec]

/-- The weight elements of occurring weights are nonzero. -/
theorem weightElement_ne_zero {m : I → ℤ} (hm : m ∈ weightSupport ρ I i) :
    weightElement i m ≠ 0 := by
  intro h0
  apply (mem_weightSupport _ _ _ m).mp hm
  apply Matrix.ext_of_mulVec_single
  intro c
  rw [Matrix.zero_mulVec]
  have h := weight_mulVec_repr i m (b.equivFun.symm (Pi.single c 1))
  rw [h0, mul_zero, map_zero, Finsupp.coe_zero, ← Module.Basis.equivFun_apply,
    LinearEquiv.apply_symm_apply] at h
  exact h

/-- The inverse universal unit is `∑ₘ Xᵐ ⊗ eₘ` over the weights. -/
theorem universalUnit_inv_eq_sum :
    (((universalUnit i)⁻¹ : (R' ⊗[K] A)ˣ) : R' ⊗[K] A) =
      ∑ m ∈ weightSupport ρ I i,
        AddMonoidAlgebra.single m (1 : K) ⊗ₜ[K] weightElement i m := by
  apply ext_coeffTensor b
  intro n
  rw [map_sum]
  simp_rw [coeffTensor_tmul, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ite_smul,
    one_smul, zero_smul]
  exact (sum_ite_eq_of_weightSupport ρ I i (weightElement i)
    (fun m hm => weightElement_eq_zero i hm) n).symm

/-- Faithfulness forces the occurring weights to generate the full lattice. -/
theorem closure_weightSupport (hi : Mono i.hom.hom.left) :
    AddSubgroup.closure (weightSupport ρ I i : Set (I → ℤ)) = ⊤ := by
  let : Mono i.hom.hom.left := hi
  have hmono : Mono (i.hom.hom ≫ (ρ).hom.hom).left := by
    change Mono (i.hom.hom.left ≫ (ρ).hom.hom.left)
    infer_instance
  have h := closure_weights_eq_top ρ I i hmono
  have hs : {m : I → ℤ | weight ρ I i m ≠ 0} =
      (weightSupport ρ I i : Set (I → ℤ)) := by
    ext m
    exact (mem_weightSupport ρ I i m).symm
  rwa [hs] at h

end Langlands.GroupScheme.FiniteAlgebraTorusWeights
