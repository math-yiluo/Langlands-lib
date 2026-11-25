/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LatticeSheafBasic

/-!
# Lattice images of matrices of continuous sections

Source: Bhatt--Scholze, Proposition 6.8.4(6), continuous changes of integral basis
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Matrix

namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Scheme.{u}) (K : Type u) [Field K]
  [TopologicalSpace K] [IsTopologicalRing K] (A : Subring K) (U : X.ProEt) (n : ℕ)

/-- The embedded lattice image of a matrix of continuous rational coefficient sections.
Source: Bhatt--Scholze, Proposition 6.8.4(6), continuous matrices in a rational frame
(auxiliary; not a blueprint node). -/
noncomputable def sectionMatrixLatticeImage (T : (Over U)ᵒᵖ)
    (g : Matrix.GeneralLinearGroup (Fin n)
      ((latticeCoefficientSheaf X K).obj.obj (op T.unop.left))) :
    Set ((latticeFreeSheaf X K U n).val.obj T) :=
  Set.range fun b : Fin n → (latticeCoefficientSheaf X A).obj.obj (op T.unop.left) ↦
    ∑ i : Fin n,
      (∑ j : Fin n, g.val i j *
        (latticeCoefficientSheafMap X A.subtype continuous_subtype_val).hom.app
          (op T.unop.left) (b j)) •
      (SheafOfModules.ιFree (R := (latticeModuleRing X K).over U)
        (ULift.up i : ULift.{u + 1} (Fin n))).val.app T
          (1 : (latticeModuleRing X K).obj.obj (op T.unop.left))

private theorem sectionMatrixLatticeImage_integral_mul_subset (T : (Over U)ᵒᵖ)
    (g : Matrix.GeneralLinearGroup (Fin n)
      ((latticeCoefficientSheaf X K).obj.obj (op T.unop.left)))
    (h : Matrix.GeneralLinearGroup (Fin n)
      ((latticeCoefficientSheaf X A).obj.obj (op T.unop.left))) :
    sectionMatrixLatticeImage X K A U n T
        (g * Matrix.GeneralLinearGroup.map
          (((latticeCoefficientSheafMap X A.subtype continuous_subtype_val).hom.app
            (op T.unop.left)).hom) h) ⊆
      sectionMatrixLatticeImage X K A U n T g := by
  let φ := ((latticeCoefficientSheafMap X A.subtype continuous_subtype_val).hom.app
    (op T.unop.left)).hom
  rintro y ⟨b, rfl⟩
  let b' := h.val *ᵥ b
  refine ⟨b', ?_⟩
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hv : (fun j ↦ φ (b' j)) = h.val.map φ *ᵥ (fun j ↦ φ (b j)) := by
    funext j
    change φ (∑ k, h.val j k * b k) = _
    simp only [map_sum, map_mul, Matrix.mulVec, dotProduct, Matrix.map_apply]
  change (g.val *ᵥ (fun j ↦ φ (b' j))) i = _
  rw [hv, Matrix.mulVec_mulVec]
  rfl

/-- Integral invertible changes of continuous coordinates preserve the lattice image.
Source: Bhatt--Scholze, Proposition 6.8.4(6), continuous integral changes of basis
(auxiliary; not a blueprint node).
Proof: multiply the integral coefficient vector by the integral matrix. Associativity of
matrix action identifies the resulting rational vector. The inverse matrix gives the
reverse inclusion, including for the empty basis. -/
theorem sectionMatrixLatticeImage_integral_mul (T : (Over U)ᵒᵖ)
    (g : Matrix.GeneralLinearGroup (Fin n)
      ((latticeCoefficientSheaf X K).obj.obj (op T.unop.left)))
    (h : Matrix.GeneralLinearGroup (Fin n)
      ((latticeCoefficientSheaf X A).obj.obj (op T.unop.left))) :
    sectionMatrixLatticeImage X K A U n T
        (g * Matrix.GeneralLinearGroup.map
          (((latticeCoefficientSheafMap X A.subtype continuous_subtype_val).hom.app
            (op T.unop.left)).hom) h) =
      sectionMatrixLatticeImage X K A U n T g := by
  apply Set.Subset.antisymm
    (sectionMatrixLatticeImage_integral_mul_subset X K A U n T g h)
  have hh := sectionMatrixLatticeImage_integral_mul_subset X K A U n T
    (g * Matrix.GeneralLinearGroup.map
      (((latticeCoefficientSheafMap X A.subtype continuous_subtype_val).hom.app
        (op T.unop.left)).hom) h) h⁻¹
  simpa only [map_inv, mul_assoc, mul_inv_cancel, mul_one] using hh

/-- The section-matrix construction specializes to the existing constant lattice image.
Source: Bhatt--Scholze, Proposition 6.8.4(6), constant versus continuous matrices
(auxiliary; not a blueprint node).
Proof: the entries of a mapped constant matrix are its constant coefficient sections. -/
theorem sectionMatrixLatticeImage_constant (T : (Over U)ᵒᵖ)
    (g : Matrix.GeneralLinearGroup (Fin n) K) :
    sectionMatrixLatticeImage X K A U n T
        (Matrix.GeneralLinearGroup.map (latticeConstantRingHom X K T.unop.left) g) =
      matrixLatticeImage X K A U n g T := rfl

omit U in
/-- A matrix of continuous rational sections with integral pointwise values and inverse
comes from an invertible matrix of continuous integral sections.
Source: Bhatt--Scholze, Proposition 6.8.4(6), integral continuous change matrices
(auxiliary; not a blueprint node).
Proof: each coefficient of the matrix and inverse has its values in the subring.
Give it that subtype codomain; continuity follows from the induced topology.
The coefficient inclusion is injective, so the inverse matrix equations descend to
integral coefficients. The resulting integral unit maps to the given rational unit. -/
theorem coefficientMatrix_integral_of_pointwise (V : X.ProEt)
    (g : Matrix.GeneralLinearGroup (Fin n) ((latticeCoefficientSheaf X K).obj.obj (op V)))
    (hg : ∀ x : V.left,
      Matrix.GeneralLinearGroup.map (latticeEvaluationRingHom X K V x) g ∈
        integralMatrixSubgroup A n) :
    ∃ h : Matrix.GeneralLinearGroup (Fin n)
        ((latticeCoefficientSheaf X A).obj.obj (op V)),
      Matrix.GeneralLinearGroup.map
        (((latticeCoefficientSheafMap X A.subtype continuous_subtype_val).hom.app
          (op V)).hom) h = g := by
  have hentries (x : V.left) :
      (∀ i j, (g.val i j).down x ∈ A) ∧
      (∀ i j, ((g⁻¹).val i j).down x ∈ A) := by
    have h := (integralMatrixSubgroup_mem_iff K A n _).mp (hg x)
    constructor
    · exact h.1
    · intro i j
      have hh := h.2 i j
      rw [← map_inv] at hh
      exact hh
  let m : Matrix (Fin n) (Fin n) ((latticeCoefficientSheaf X A).obj.obj (op V)) :=
    fun i j ↦ ULift.up
      ⟨fun x ↦ ⟨(g.val i j).down x, (hentries x).1 i j⟩,
        Continuous.subtype_mk (g.val i j).down.continuous _⟩
  let mi : Matrix (Fin n) (Fin n) ((latticeCoefficientSheaf X A).obj.obj (op V)) :=
    fun i j ↦ ULift.up
      ⟨fun x ↦ ⟨((g⁻¹).val i j).down x, (hentries x).2 i j⟩,
        Continuous.subtype_mk ((g⁻¹).val i j).down.continuous _⟩
  let φ := ((latticeCoefficientSheafMap X A.subtype continuous_subtype_val).hom.app
    (op V)).hom
  have hφ : Function.Injective φ := by
    intro f g h
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun s ↦ s.down x) h
  let f : Matrix (Fin n) (Fin n)
      ((latticeCoefficientSheaf X A).obj.obj (op V)) →+*
      Matrix (Fin n) (Fin n) ((latticeCoefficientSheaf X K).obj.obj (op V)) :=
    RingHom.mapMatrix φ
  have hf : Function.Injective f := Matrix.map_injective hφ
  have hm : f m = g.val := by ext i j; rfl
  have hmi : f mi = (g⁻¹).val := by ext i j; rfl
  have hl : m * mi = 1 := by
    apply hf
    rw [map_mul, map_one, hm, hmi]
    exact congrArg Units.val (mul_inv_cancel g)
  have hr : mi * m = 1 := by
    apply hf
    rw [map_mul, map_one, hm, hmi]
    exact congrArg Units.val (inv_mul_cancel g)
  refine ⟨⟨m, mi, hl, hr⟩, ?_⟩
  apply Units.ext
  exact hm

/-- Pointwise equality of a continuous matrix coset to a constant coset identifies lattice images.
Source: Bhatt--Scholze, Proposition 6.8.4(6), local constancy of embedded lattices
(auxiliary; not a blueprint node).
Proof: the pointwise change matrix is integral together with its inverse, so the previous
coefficient-lifting lemma gives an invertible integral continuous matrix. Multiplication
by it preserves the lattice image. -/
theorem sectionMatrixLatticeImage_eq_of_pointwise_coset (T : (Over U)ᵒᵖ)
    (g : Matrix.GeneralLinearGroup (Fin n)
      ((latticeCoefficientSheaf X K).obj.obj (op T.unop.left)))
    (h : Matrix.GeneralLinearGroup (Fin n) K)
    (hgh : ∀ x : T.unop.left.left,
      (Quotient.mk _ h : integralMatrixCosets A n) =
        Quotient.mk _ (Matrix.GeneralLinearGroup.map
          (latticeEvaluationRingHom X K T.unop.left x) g)) :
    sectionMatrixLatticeImage X K A U n T g = matrixLatticeImage X K A U n h T := by
  let hc := Matrix.GeneralLinearGroup.map (latticeConstantRingHom X K T.unop.left) h
  obtain ⟨k, hk⟩ := coefficientMatrix_integral_of_pointwise X K A n T.unop.left
    (hc⁻¹ * g) (fun x ↦ by
      have hconst : Matrix.GeneralLinearGroup.map
          (latticeEvaluationRingHom X K T.unop.left x) hc = h := by
        apply Units.ext
        ext i j
        rfl
      rw [map_mul, map_inv, hconst]
      exact QuotientGroup.leftRel_apply.mp (Quotient.exact (hgh x)))
  have heq : g = hc * Matrix.GeneralLinearGroup.map
      (((latticeCoefficientSheafMap X A.subtype continuous_subtype_val).hom.app
        (op T.unop.left)).hom) k := by
    rw [hk, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [heq, sectionMatrixLatticeImage_integral_mul]
  exact sectionMatrixLatticeImage_constant X K A U n T h

end AlgebraicGeometry.ProEtale
