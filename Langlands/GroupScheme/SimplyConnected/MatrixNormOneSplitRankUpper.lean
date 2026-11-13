import Langlands.GroupScheme.SimplyConnected.MatrixNormOneSplitRankAlgebra
import Langlands.GroupScheme.Torus.RingRepresentationWeights
import Langlands.GroupScheme.FiniteAlgebraRightRegularAffine
import Langlands.GroupScheme.CentralSimpleNormOne
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.Algebra.ReducedNormRegular

/-!
# Upper bound for the split rank of `SL_m(D)`

For a closed split torus `𝔾ₘ^I → SL_1(A)` in the reduced-norm-one group of a
finite-dimensional central simple algebra `A`, the inverse of the universal torus point
expands as `∑ₘ Xᵐ ⊗ eₘ` over the weights `m` of the inverse-right-regular representation.
The coefficients `eₘ` form a complete family of nonzero orthogonal idempotents of `A`, the
weights generate `ℤ^I`, and the reduced-norm-one condition gives the relation
`∑ₘ dim (eₘ A) · m = 0`. For `A = M_n(D)` every right ideal `eₘ A` has dimension at least
`n · dim D`, so there are at most `n` weights and `|I| ≤ n - 1`.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct Matrix

namespace Langlands.GroupScheme.MatrixNormOneSplitRank

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! ### Coefficients of elements of `K[Λ] ⊗ A` -/

section Coefficients

variable {K A Λ : Type*} [Field K] [Ring A] [Algebra K A] [AddCommMonoid Λ]

/-- The coefficient of the monomial `m`, as a `K`-linear form on `K[Λ]`. -/
def coeffForm (m : Λ) : AddMonoidAlgebra K Λ →ₗ[K] K :=
  Finsupp.lapply m ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap

omit [Ring A] [Algebra K A] [AddCommMonoid Λ] in
theorem coeffForm_apply (m : Λ) (p : AddMonoidAlgebra K Λ) : coeffForm m p = p.coeff m := rfl

variable (A) in
/-- The coefficient of the monomial `m` of an element of `K[Λ] ⊗ A`, an element of `A`. -/
def coeffTensor (m : Λ) : AddMonoidAlgebra K Λ ⊗[K] A →ₗ[K] A :=
  (TensorProduct.lid K A).toLinearMap ∘ₗ TensorProduct.map (coeffForm m) LinearMap.id

omit [AddCommMonoid Λ] in
theorem coeffTensor_tmul (m : Λ) (p : AddMonoidAlgebra K Λ) (x : A) :
    coeffTensor A m (p ⊗ₜ x) = p.coeff m • x := rfl

/-- Coordinates of a coefficient are coefficients of coordinates. -/
theorem repr_coeffTensor {ι : Type*} (b : Module.Basis ι K A) (m : Λ)
    (z : AddMonoidAlgebra K Λ ⊗[K] A) (a : ι) :
    b.repr (coeffTensor A m z) a = ((b.baseChange (AddMonoidAlgebra K Λ)).repr z a).coeff m := by
  induction z using TensorProduct.inductionOn with
  | tmul p x =>
    rw [coeffTensor_tmul, Module.Basis.baseChange_repr_tmul, map_smul, Finsupp.smul_apply,
      smul_eq_mul, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul, mul_comm]
  | add z z' hz hz' =>
    rw [map_add, map_add, Finsupp.add_apply, hz, hz', map_add, Finsupp.add_apply,
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply]

/-- An element of `K[Λ] ⊗ A` is determined by its coefficients. -/
theorem ext_coeffTensor {ι : Type*} (b : Module.Basis ι K A)
    {z z' : AddMonoidAlgebra K Λ ⊗[K] A} (h : ∀ m, coeffTensor A m z = coeffTensor A m z') :
    z = z' := by
  apply (b.baseChange (AddMonoidAlgebra K Λ)).repr.injective
  ext a m
  rw [← repr_coeffTensor b, ← repr_coeffTensor b, h]

/-- Taking coefficients is left `A`-linear. -/
theorem coeffTensor_one_tmul_mul (m : Λ) (x : A) (z : AddMonoidAlgebra K Λ ⊗[K] A) :
    coeffTensor A m (((1 : AddMonoidAlgebra K Λ) ⊗ₜ[K] x) * z) = x * coeffTensor A m z := by
  induction z using TensorProduct.inductionOn with
  | tmul p y =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, coeffTensor_tmul, coeffTensor_tmul,
      mul_smul_comm]
  | add z z' hz hz' => rw [mul_add, map_add, map_add, hz, hz', mul_add]

end Coefficients

/-! ### The weight idempotents of a split torus in `SL_1(A)` -/

section Weights

open SplitTorusRepresentationWeights CentralSimpleUnits

variable {K A : Type u} [Field K] [Ring A] [Algebra K A]
  [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]
  {I : Type u} [Fintype I] [DecidableEq I]
  (i : splitTorus (Spec (CommRingCat.of K)) I ⟶ normOne K A)

/-- The coefficient algebra `K[ℤ^I]` of the universal torus point. -/
local notation "R'" => AddMonoidAlgebra K (I → ℤ)

/-- The inverse-right-regular representation of the unit group of `A`. -/
local notation "ρ" => FiniteAlgebraUnits.rightRegularRepresentation (Module.finBasis K A)

/-- The universal torus point, as a reduced-norm-one unit of `K[ℤ^I] ⊗ A`. -/
def universalUnit : (R' ⊗[K] A)ˣ :=
  (normOneAffinePointsEquiv K A (CommAlgCat.of (CommRingCat.of K) R')
    (splitTorus.universalPoint (R := CommRingCat.of K) I ≫ i.hom.hom) : (R' ⊗[K] A)ˣ)

theorem universalUnit_eq :
    universalUnit i = FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis K A)
      (CommAlgCat.of (CommRingCat.of K) R')
      (splitTorus.universalPoint (R := CommRingCat.of K) I ≫
        (i ≫ normOneι K A).hom.hom) := by
  rw [Grp.comp_hom_hom, ← Category.assoc]
  rfl

/-- The coefficient elements `eₘ` of the inverse of the universal unit. -/
def weightElement (m : I → ℤ) : A :=
  coeffTensor (K := K) A m (((universalUnit i)⁻¹ : (R' ⊗[K] A)ˣ) : R' ⊗[K] A)

/-- **Weights act by right multiplication.** The weight matrix `Pₘ` of the
inverse-right-regular representation is the matrix of right multiplication by `eₘ`. -/
theorem weight_mulVec_repr (m : I → ℤ) (x : A) :
    weight ρ I (i ≫ normOneι K A) m *ᵥ ⇑((Module.finBasis K A).repr x) =
      ⇑((Module.finBasis K A).repr (x * weightElement i m)) := by
  set b := Module.finBasis K A
  set Rc := CommAlgCat.of (CommRingCat.of K) R'
  set pt := splitTorus.universalPoint (R := CommRingCat.of K) I
  have h := FiniteAlgebraUnits.affineMatrix_rightRegular_mulVec_repr b Rc
    (pt ≫ (i ≫ normOneι K A).hom.hom) ((1 : R') ⊗ₜ[K] x)
  have hU : ((MatrixRepresentation.affineMatrix ρ Rc (pt ≫ (i ≫ normOneι K A).hom.hom) :
      Matrix (Fin (Module.finrank K A)) (Fin (Module.finrank K A)) R')) =
      (universalMatrix ρ I (i ≫ normOneι K A) :
        Matrix (Fin (Module.finrank K A)) (Fin (Module.finrank K A)) R') := by
    rw [MatrixRepresentation.affineMatrix_apply, Category.assoc]
    rfl
  rw [hU, ← universalUnit_eq] at h
  funext a
  calc (weight ρ I (i ≫ normOneι K A) m *ᵥ ⇑(b.repr x)) a
      = coeffForm m (((universalMatrix ρ I (i ≫ normOneι K A) :
          Matrix (Fin (Module.finrank K A)) (Fin (Module.finrank K A)) R') *ᵥ
            ⇑((b.baseChange R').repr ((1 : R') ⊗ₜ[K] x))) a) := by
        simp only [Matrix.mulVec, dotProduct, map_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Module.Basis.baseChange_repr_tmul, mul_smul_comm, mul_one, map_smul, smul_eq_mul,
          mul_comm]
        rfl
    _ = coeffForm m ((b.baseChange R').repr
          (((1 : R') ⊗ₜ[K] x) * ((universalUnit i)⁻¹ : (R' ⊗[K] A)ˣ)) a) := by
        rw [h]
    _ = b.repr (x * weightElement i m) a := by
        rw [coeffForm_apply, ← repr_coeffTensor, coeffTensor_one_tmul_mul]
        rfl

theorem weightElement_eq_zero {m : I → ℤ} (hm : m ∉ weightSupport ρ I (i ≫ normOneι K A)) :
    weightElement i m = 0 := by
  have h := weight_mulVec_repr i m 1
  rw [weight_eq_zero _ _ _ hm, Matrix.zero_mulVec, one_mul] at h
  apply (Module.finBasis K A).repr.injective
  ext a
  simpa using (congrFun h a).symm

theorem repr_weightElement (m : I → ℤ) :
    ⇑((Module.finBasis K A).repr (weightElement i m)) =
      weight ρ I (i ≫ normOneι K A) m *ᵥ ⇑((Module.finBasis K A).repr 1) := by
  rw [weight_mulVec_repr, one_mul]

/-- The weight elements are orthogonal idempotents. -/
theorem weightElement_mul (m n : I → ℤ) :
    weightElement i m * weightElement i n = if m = n then weightElement i m else 0 := by
  apply (Module.finBasis K A).repr.injective
  apply DFunLike.coe_injective
  rw [← weight_mulVec_repr, repr_weightElement, Matrix.mulVec_mulVec, weight_mul_weight]
  by_cases h : n = m
  · subst h
    rw [ite_eq_left rfl, ite_eq_left rfl, repr_weightElement]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h), Matrix.zero_mulVec, map_zero,
      Finsupp.coe_zero]

/-- The weight elements add up to `1`. -/
theorem sum_weightElement :
    ∑ m ∈ weightSupport ρ I (i ≫ normOneι K A), weightElement i m = 1 := by
  apply (Module.finBasis K A).repr.injective
  apply DFunLike.coe_injective
  rw [map_sum, Finsupp.coe_finsetSum, Finset.sum_congr rfl fun m _ => repr_weightElement i m,
    ← Matrix.sum_mulVec, sum_weight, Matrix.one_mulVec]

/-- The weight elements of occurring weights are nonzero. -/
theorem weightElement_ne_zero {m : I → ℤ} (hm : m ∈ weightSupport ρ I (i ≫ normOneι K A)) :
    weightElement i m ≠ 0 := by
  intro h0
  apply (mem_weightSupport _ _ _ m).mp hm
  apply Matrix.ext_of_mulVec_single
  intro c
  rw [Matrix.zero_mulVec]
  have h := weight_mulVec_repr i m ((Module.finBasis K A).equivFun.symm (Pi.single c 1))
  rw [h0, mul_zero, map_zero, Finsupp.coe_zero, ← Module.Basis.equivFun_apply,
    LinearEquiv.apply_symm_apply] at h
  exact h

/-- The inverse universal unit is `∑ₘ Xᵐ ⊗ eₘ` over the weights. -/
theorem universalUnit_inv_eq_sum :
    (((universalUnit i)⁻¹ : (R' ⊗[K] A)ˣ) : R' ⊗[K] A) =
      ∑ m ∈ weightSupport ρ I (i ≫ normOneι K A),
        AddMonoidAlgebra.single m (1 : K) ⊗ₜ[K] weightElement i m := by
  apply ext_coeffTensor (Module.finBasis K A)
  intro n
  rw [map_sum]
  simp_rw [coeffTensor_tmul, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ite_smul,
    one_smul, zero_smul]
  exact (sum_ite_eq_of_weightSupport ρ I (i ≫ normOneι K A) (weightElement i)
    (fun m hm => weightElement_eq_zero i hm) n).symm

/-- The regular norm of the inverse universal unit is `1`. -/
theorem norm_universalUnit_inv :
    Algebra.norm R' (((universalUnit i)⁻¹ : (R' ⊗[K] A)ˣ) : R' ⊗[K] A) = 1 := by
  rw [Langlands.CentralSimple.norm_eq_reducedNorm_pow]
  have hmem : (universalUnit i)⁻¹ ∈ Langlands.CentralSimple.reducedNormOne K A R' :=
    (Langlands.CentralSimple.reducedNormOne K A R').inv_mem
      (normOneAffinePointsEquiv K A (CommAlgCat.of (CommRingCat.of K) R')
        (splitTorus.universalPoint (R := CommRingCat.of K) I ≫ i.hom.hom)).2
  rw [Langlands.CentralSimple.mem_reducedNormOne] at hmem
  rw [hmem, one_pow]

/-- **The weight relation.** The dimensions of the right ideals `eₘ A` weight the
occurring characters to zero. -/
theorem sum_finrank_smul_eq_zero :
    ∑ m ∈ weightSupport ρ I (i ≫ normOneι K A),
      Module.finrank K (LinearMap.range (LinearMap.mulLeft K (weightElement i m))) • m = 0 := by
  classical
  set S := weightSupport ρ I (i ≫ normOneι K A)
  let e : S → A := fun s => weightElement i s.1
  have hmul : ∀ s t : S, e s * e t = if s = t then e s else 0 := by
    intro s t
    simp only [e, weightElement_mul, Subtype.ext_iff]
  have hsum : ∑ s, e s = 1 := by
    rw [Finset.sum_coe_sort S (weightElement i)]
    exact sum_weightElement i
  have hnorm := norm_sum_tmul (K := K) hmul hsum R' fun s => AddMonoidAlgebra.single s.1 (1 : K)
  have hinv : (∑ s, AddMonoidAlgebra.single s.1 (1 : K) ⊗ₜ[K] e s) =
      (((universalUnit i)⁻¹ : (R' ⊗[K] A)ˣ) : R' ⊗[K] A) := by
    rw [universalUnit_inv_eq_sum]
    exact Finset.sum_coe_sort S fun m => AddMonoidAlgebra.single m (1 : K) ⊗ₜ[K] weightElement i m
  rw [hinv, norm_universalUnit_inv] at hnorm
  simp_rw [AddMonoidAlgebra.single_pow, one_pow] at hnorm
  rw [AddMonoidAlgebra.prod_single, Finset.prod_const_one, AddMonoidAlgebra.one_def] at hnorm
  have h := congrArg AddMonoidAlgebra.coeff hnorm
  rw [AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single] at h
  have h' := (Finsupp.single_left_injective one_ne_zero h).symm
  rw [← h']
  exact (Finset.sum_coe_sort S fun m =>
    Module.finrank K (LinearMap.range (LinearMap.mulLeft K (weightElement i m))) • m).symm

/-- The occurring weights generate the character lattice `ℤ^I` when the torus is closed. -/
theorem closure_weightSupport (hi : IsClosedSubgroup i) :
    AddSubgroup.closure (weightSupport ρ I (i ≫ normOneι K A) : Set (I → ℤ)) = ⊤ := by
  have hmono : Mono ((i ≫ normOneι K A).hom.hom ≫ (ρ).hom.hom).left := by
    have : IsClosedImmersion i.hom.hom.left := hi
    have : IsClosedImmersion (normOneι K A).hom.hom.left := normOne_isClosedSubgroup K A
    show Mono ((i.hom.hom.left ≫ (normOneι K A).hom.hom.left) ≫ (ρ).hom.hom.left)
    infer_instance
  have h := closure_weights_eq_top ρ I (i ≫ normOneι K A) hmono
  have hs : {m : I → ℤ | weight ρ I (i ≫ normOneι K A) m ≠ 0} =
      (weightSupport ρ I (i ≫ normOneι K A) : Set (I → ℤ)) := by
    ext m
    exact (mem_weightSupport _ _ _ m).symm
  rwa [hs] at h

end Weights

/-! ### The bound for matrix algebras over division algebras -/

section Matrix

open SplitTorusRepresentationWeights CentralSimpleUnits

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  [Algebra.IsCentral K D] {n : ℕ} [NeZero n]

/-- **Upper bound.** A closed split torus `𝔾ₘ^I` in `SL_n(D)` has `|I| ≤ n - 1`. -/
theorem card_le_of_isClosedSubgroup (I : Type u) [Fintype I] [DecidableEq I]
    (i : splitTorus (Spec (CommRingCat.of K)) I ⟶ normOne K (Matrix (Fin n) (Fin n) D))
    (hi : IsClosedSubgroup i) : Fintype.card I ≤ n - 1 := by
  classical
  set S := weightSupport (FiniteAlgebraUnits.rightRegularRepresentation
    (Module.finBasis K (Matrix (Fin n) (Fin n) D))) I (i ≫ normOneι K _)
  let r : (I → ℤ) → ℕ := fun m =>
    Module.finrank K (LinearMap.range (LinearMap.mulLeft K (weightElement i m)))
  have hD : 0 < Module.finrank K D := Module.finrank_pos
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hlow : ∀ m ∈ S, n * Module.finrank K D ≤ r m := fun m hm =>
    le_finrank_range_mulLeft _ (weightElement_ne_zero i hm)
  have hcard := card_add_one_le_of_relation S (closure_weightSupport i hi) r
    (fun m hm => lt_of_lt_of_le (Nat.mul_pos hn hD) (hlow m hm)) (sum_finrank_smul_eq_zero i)
  -- the right ideals `eₘ A` fill `A`
  let e : S → Matrix (Fin n) (Fin n) D := fun s => weightElement i s.1
  have hmul : ∀ s t : S, e s * e t = if s = t then e s else 0 := by
    intro s t
    simp only [e, weightElement_mul, Subtype.ext_iff]
  have hsum : ∑ s, e s = 1 := by
    rw [Finset.sum_coe_sort S (weightElement i)]
    exact sum_weightElement i
  have hdim := sum_finrank_piece (K := K) hmul hsum
  rw [Module.finrank_matrix, Fintype.card_fin] at hdim
  have hS : S.card * (n * Module.finrank K D) ≤ n * (n * Module.finrank K D) := by
    calc S.card * (n * Module.finrank K D) = ∑ s : S, n * Module.finrank K D := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]
      _ ≤ ∑ s : S, r s.1 := Finset.sum_le_sum fun s _ => hlow s.1 s.2
      _ = n * n * Module.finrank K D := hdim
      _ = n * (n * Module.finrank K D) := by ring
  have hSn : S.card ≤ n := Nat.le_of_mul_le_mul_right hS (Nat.mul_pos hn hD)
  omega

/-- **Upper bound for the split rank.** -/
theorem splitRank_le :
    splitRank (normOne K (Matrix (Fin n) (Fin n) D)) ≤ ((n - 1 : ℕ) : ℕ∞) := by
  refine iSup_le fun I => iSup_le fun hI => iSup_le fun i => iSup_le fun hi => ?_
  classical
  have := Fintype.ofFinite I
  rw [Nat.card_eq_fintype_card]
  exact_mod_cast card_le_of_isClosedSubgroup I i hi

end Matrix

end Langlands.GroupScheme.MatrixNormOneSplitRank
