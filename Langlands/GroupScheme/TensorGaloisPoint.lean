import Langlands.GroupScheme.Torus.CocharacterDatum
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Flat.Basic

/-! # Galois descent on tensor-valued affine points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme.TensorGaloisPoint

set_option backward.isDefEq.respectTransparency false

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    (A : Type u) [CommRing A] [Algebra k A]

/-- Conjugate the field factor and fix the test algebra. -/
def coefficientConjugate (σ : K ≃ₐ[k] K) : K ⊗[k] A →ₐ[k] K ⊗[k] A :=
  Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id k A)

@[simp]
theorem coefficientConjugate_tmul (σ : K ≃ₐ[k] K) (c : K) (a : A) :
    coefficientConjugate k K A σ (c ⊗ₜ[k] a) = σ c ⊗ₜ[k] a := rfl

@[simp]
theorem coefficientConjugate_one :
    coefficientConjugate k K A 1 = AlgHom.id k (K ⊗[k] A) := by
  exact Algebra.TensorProduct.map_id

@[simp]
theorem coefficientConjugate_mul (σ τ : K ≃ₐ[k] K) :
    coefficientConjugate k K A (σ * τ) =
      (coefficientConjugate k K A σ).comp (coefficientConjugate k K A τ) := by
  ext <;> simp

/-- On a scalar-extended basis, conjugation acts on the coefficients. -/
theorem repr_coefficientConjugate {I : Type u} (b : Module.Basis I k A)
    (σ : K ≃ₐ[k] K) (x : K ⊗[k] A) (i : I) :
    (b.baseChange K).repr (coefficientConjugate k K A σ x) i =
      σ ((b.baseChange K).repr x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul c a => simp [Algebra.smul_def]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

/-- The fixed tensors are exactly the image of the test algebra. -/
theorem mem_range_includeRight_iff [FiniteDimensional k K] [IsGalois k K]
    (x : K ⊗[k] A) :
    x ∈ (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).range ↔
      ∀ σ : K ≃ₐ[k] K, coefficientConjugate k K A σ x = x := by
  classical
  constructor
  · rintro ⟨a, rfl⟩ σ
    simp [Algebra.TensorProduct.includeRight_apply]
  · intro hx
    let b := Module.Free.chooseBasis k A
    let v := (b.baseChange K).repr x
    have hv : ∀ i, v i ∈ Set.range (algebraMap k K) := by
      intro i
      apply (IsGalois.mem_range_algebraMap_iff_fixed _).mpr
      intro σ
      change σ ((b.baseChange K).repr x i) = (b.baseChange K).repr x i
      rw [← repr_coefficientConjugate, hx σ]
    choose c hc using hv
    refine ⟨∑ i ∈ v.support, c i • b i, ?_⟩
    change (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A)
      (∑ i ∈ v.support, c i • b i) = x
    calc
      _ = ∑ i ∈ v.support, v i • (b.baseChange K) i := by
        simp only [map_sum, map_smul]
        apply Finset.sum_congr rfl
        intro i _
        rw [← hc i, Module.Basis.baseChange_apply]
        simp [Algebra.TensorProduct.includeRight_apply, Algebra.smul_def]
      _ = x := by
        simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using
          (b.baseChange K).linearCombination_repr x

variable (G : GroupScheme (Spec (CommRingCat.of k)))

/-- Galois conjugation on the field factor of an actual tensor-valued point. -/
def conjugate (σ : K ≃ₐ[k] K) :
    Lie.AffinePoints G (K ⊗[k] A) →* Lie.AffinePoints G (K ⊗[k] A) :=
  Lie.affineMap G (coefficientConjugate k K A σ)

@[simp]
theorem conjugate_one (x : Lie.AffinePoints G (K ⊗[k] A)) :
    conjugate k K A G 1 x = x := by
  rw [conjugate, coefficientConjugate_one]
  exact Lie.affineMap_id G x

@[simp]
theorem conjugate_mul (σ τ : K ≃ₐ[k] K) (x : Lie.AffinePoints G (K ⊗[k] A)) :
    conjugate k K A G (σ * τ) x =
      conjugate k K A G σ (conjugate k K A G τ x) := by
  rw [conjugate, coefficientConjugate_mul, Lie.affineMap_comp]
  rfl

/-- Extend a test-algebra point along `a ↦ 1 ⊗ a`. -/
def extend : Lie.AffinePoints G A →* Lie.AffinePoints G (K ⊗[k] A) :=
  Lie.affineMap G Algebra.TensorProduct.includeRight

@[simp]
theorem conjugate_extend (σ : K ≃ₐ[k] K) (x : Lie.AffinePoints G A) :
    conjugate k K A G σ (extend k K A G x) = extend k K A G x := by
  rw [conjugate, extend, ← Lie.affineMap_comp]
  have h : (coefficientConjugate k K A σ).comp Algebra.TensorProduct.includeRight =
      (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A) := by
    ext a
    simp [Algebra.TensorProduct.includeRight_apply]
  rw [h]

/-- Fixed points for every coefficient automorphism. -/
def fixedSubgroup : Subgroup (Lie.AffinePoints G (K ⊗[k] A)) where
  carrier := {x | ∀ σ : K ≃ₐ[k] K, conjugate k K A G σ x = x}
  one_mem' σ := map_one _
  mul_mem' hx hy σ := by rw [map_mul, hx σ, hy σ]
  inv_mem' hx σ := by rw [map_inv, hx σ]

@[simp]
theorem mem_fixedSubgroup (x : Lie.AffinePoints G (K ⊗[k] A)) :
    x ∈ fixedSubgroup k K A G ↔ ∀ σ : K ≃ₐ[k] K, conjugate k K A G σ x = x := Iff.rfl

variable [IsAffine G.X.left]

/-- Coefficient extension is injective on actual affine points. -/
theorem extend_injective : Function.Injective (extend k K A G) :=
  CocharacterDatum.affineMap_injective _
    (Algebra.TensorProduct.includeRight_injective (algebraMap k K).injective)

variable [FiniteDimensional k K] [IsGalois k K]

/-- A fixed tensor-valued point descends to the test algebra. -/
theorem exists_extend_eq (x : fixedSubgroup k K A G) :
    ∃ y : Lie.AffinePoints G A, extend k K A G y = x.val := by
  apply CocharacterDatum.exists_affineMap_eq _
    (Algebra.TensorProduct.includeRight_injective (algebraMap k K).injective)
  intro c
  apply (mem_range_includeRight_iff k K A _).mpr
  intro σ
  have h := congrArg (fun z => (CocharacterDatum.coord z).hom c) (x.property σ)
  rw [conjugate, CocharacterDatum.coord_affineMap] at h
  exact h

/-- Choose the unique descended actual point. -/
def descend (x : fixedSubgroup k K A G) : Lie.AffinePoints G A :=
  (exists_extend_eq k K A G x).choose

@[simp]
theorem extend_descend (x : fixedSubgroup k K A G) :
    extend k K A G (descend k K A G x) = x.val :=
  (exists_extend_eq k K A G x).choose_spec

/-- Test-algebra points are multiplicatively equivalent to fixed tensor-valued points. -/
def fixedEquiv : Lie.AffinePoints G A ≃* fixedSubgroup k K A G where
  toFun x := ⟨extend k K A G x, fun σ => conjugate_extend k K A G σ x⟩
  invFun := descend k K A G
  left_inv _ := extend_injective k K A G (extend_descend k K A G _)
  right_inv x := Subtype.ext (extend_descend k K A G x)
  map_mul' x y := Subtype.ext (map_mul (extend k K A G) x y)

/-- Descent characterizes the image of test-algebra points. -/
theorem mem_range_extend_iff (x : Lie.AffinePoints G (K ⊗[k] A)) :
    x ∈ Set.range (extend k K A G) ↔ x ∈ fixedSubgroup k K A G := by
  constructor
  · rintro ⟨y, rfl⟩ σ
    exact conjugate_extend k K A G σ y
  · intro hx
    exact exists_extend_eq k K A G ⟨x, hx⟩

section Norm

variable (Z : CommGroupScheme (Spec (CommRingCat.of k)))

omit [IsGalois k K] in
/-- Product of all Galois conjugates of a tensor-valued commutative-group point. -/
def conjugateProduct :
    Lie.AffinePoints Z.toGrp (K ⊗[k] A) →* Lie.AffinePoints Z.toGrp (K ⊗[k] A) where
  toFun x := ∏ σ : K ≃ₐ[k] K, conjugate k K A Z.toGrp σ x
  map_one' := by simp
  map_mul' x y := by simp [Finset.prod_mul_distrib]

omit [IsGalois k K] in
theorem conjugateProduct_fixed (x : Lie.AffinePoints Z.toGrp (K ⊗[k] A)) :
    conjugateProduct k K A Z x ∈ fixedSubgroup k K A Z.toGrp := by
  intro σ
  change conjugate k K A Z.toGrp σ (∏ τ : K ≃ₐ[k] K, conjugate k K A Z.toGrp τ x) = _
  rw [map_prod]
  simp only [← conjugate_mul]
  exact Fintype.prod_equiv (Equiv.mulLeft σ) _ _ (fun _ => rfl)

variable [IsAffine Z.X.left]

/-- The natural point norm descends the product of all conjugates to the test algebra. -/
def norm : Lie.AffinePoints Z.toGrp (K ⊗[k] A) →* Lie.AffinePoints Z.toGrp A :=
  (fixedEquiv k K A Z.toGrp).symm.toMonoidHom.comp
    ((conjugateProduct k K A Z).codRestrict (fixedSubgroup k K A Z.toGrp)
      (conjugateProduct_fixed k K A Z))

@[simp]
theorem extend_norm (x : Lie.AffinePoints Z.toGrp (K ⊗[k] A)) :
    extend k K A Z.toGrp (norm k K A Z x) =
      ∏ σ : K ≃ₐ[k] K, conjugate k K A Z.toGrp σ x :=
  extend_descend k K A Z.toGrp _

@[simp]
theorem norm_extend (x : Lie.AffinePoints Z.toGrp A) :
    norm k K A Z (extend k K A Z.toGrp x) = x ^ Module.finrank k K := by
  apply extend_injective k K A Z.toGrp
  rw [extend_norm, map_pow]
  simp only [conjugate_extend, Finset.prod_const, Finset.card_univ]
  rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank]

end Norm

section Naturality

variable {A} {B : Type u} [CommRing B] [Algebra k B]

/-- Change the test algebra and fix the field factor. -/
def tensorMap (f : A →ₐ[k] B) : K ⊗[k] A →ₐ[k] K ⊗[k] B :=
  Algebra.TensorProduct.map (AlgHom.id k K) f

omit [FiniteDimensional k K] [IsGalois k K] in
theorem tensorMap_coefficientConjugate (f : A →ₐ[k] B) (σ : K ≃ₐ[k] K) :
    (tensorMap k K f).comp (coefficientConjugate k K A σ) =
      (coefficientConjugate k K B σ).comp (tensorMap k K f) := by
  ext <;> simp [tensorMap]

omit [IsAffine G.X.left] [FiniteDimensional k K] [IsGalois k K] in
/-- Extending points commutes with every test-algebra map. -/
theorem extend_naturality (f : A →ₐ[k] B) (x : Lie.AffinePoints G A) :
    Lie.affineMap G (tensorMap k K f) (extend k K A G x) =
      extend k K B G (Lie.affineMap G f x) := by
  rw [extend, extend, ← Lie.affineMap_comp, ← Lie.affineMap_comp]
  have h : (tensorMap k K f).comp Algebra.TensorProduct.includeRight =
      (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B).comp f := by
    ext a
    simp [tensorMap, Algebra.TensorProduct.includeRight_apply]
  rw [h]

omit [IsAffine G.X.left] [FiniteDimensional k K] [IsGalois k K] in
/-- Conjugation commutes with every test-algebra map. -/
theorem conjugate_naturality (f : A →ₐ[k] B) (σ : K ≃ₐ[k] K)
    (x : Lie.AffinePoints G (K ⊗[k] A)) :
    Lie.affineMap G (tensorMap k K f) (conjugate k K A G σ x) =
      conjugate k K B G σ (Lie.affineMap G (tensorMap k K f) x) := by
  rw [conjugate, conjugate, ← Lie.affineMap_comp, ← Lie.affineMap_comp,
    tensorMap_coefficientConjugate]

variable (Z : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine Z.X.left]

/-- The norm commutes with every map of commutative test algebras. -/
theorem norm_naturality (f : A →ₐ[k] B)
    (x : Lie.AffinePoints Z.toGrp (K ⊗[k] A)) :
    Lie.affineMap Z.toGrp f (norm k K A Z x) =
      norm k K B Z (Lie.affineMap Z.toGrp (tensorMap k K f) x) := by
  apply extend_injective k K B Z.toGrp
  rw [← extend_naturality, extend_norm, map_prod, extend_norm]
  apply Finset.prod_congr rfl
  intro σ _
  exact conjugate_naturality k K Z.toGrp f σ x

variable {Z} {W : CommGroupScheme (Spec (CommRingCat.of k))} [IsAffine W.X.left]

/-- Actual homomorphisms of affine commutative group schemes commute with the norm. -/
theorem norm_target_naturality (f : Z ⟶ W)
    (x : Lie.AffinePoints Z.toGrp (K ⊗[k] A)) :
    GroupScheme.affinePointsTarget Z.toGrp (CommGroupScheme.groupHom f)
        (CommAlgCat.of k A) (norm k K A Z x) =
      norm k K A W
        (GroupScheme.affinePointsTarget Z.toGrp (CommGroupScheme.groupHom f)
          (CommAlgCat.of k (K ⊗[k] A)) x) := by
  apply extend_injective k K A W.toGrp
  have hn := DFunLike.congr_fun
    (GroupScheme.affinePointsTarget_naturality Z.toGrp (CommGroupScheme.groupHom f)
      (CommAlgCat.ofHom (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A)))
      (norm k K A Z x)
  change extend k K A W.toGrp
    (GroupScheme.affinePointsTarget Z.toGrp (CommGroupScheme.groupHom f) _
      (norm k K A Z x)) =
    GroupScheme.affinePointsTarget Z.toGrp (CommGroupScheme.groupHom f) _
      (extend k K A Z.toGrp (norm k K A Z x)) at hn
  rw [hn, extend_norm, map_prod, extend_norm]
  apply Finset.prod_congr rfl
  intro σ _
  exact (DFunLike.congr_fun
    (GroupScheme.affinePointsTarget_naturality Z.toGrp (CommGroupScheme.groupHom f)
      (CommAlgCat.ofHom (coefficientConjugate k K A σ))) x).symm

end Naturality

end Langlands.GroupScheme.TensorGaloisPoint
