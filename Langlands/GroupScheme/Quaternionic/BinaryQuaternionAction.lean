import Langlands.GroupScheme.Quaternionic.QuaternionConjugation
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.Flat.Basic

/-! # Binary quaternionic product action -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v

open scoped Matrix

namespace Langlands.GroupScheme.Quaternionic.BinaryAction

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

/-- Include a scalar special-linear matrix in the possibly noncommutative matrix units. -/
def scalarSL : Matrix.SpecialLinearGroup (Fin 2) R →* (Matrix (Fin 2) (Fin 2) A)ˣ :=
  (Units.map (algebraMap R A).mapMatrix.toMonoidHom).comp Matrix.SpecialLinearGroup.toGL

@[simp] theorem scalarSL_apply (g : Matrix.SpecialLinearGroup (Fin 2) R) (i j : Fin 2) :
    (scalarSL (A := A) g : Matrix (Fin 2) (Fin 2) A) i j = algebraMap R A (g i j) := rfl

/-- Uniform right multiplication on the two quaternionic coordinates. -/
def uniform : Aˣ →* (Matrix (Fin 2) (Fin 2) A)ˣ :=
  Units.map (Matrix.scalar (Fin 2)).toMonoidHom

@[simp] theorem uniform_val (b : Aˣ) :
    (uniform b : Matrix (Fin 2) (Fin 2) A) = Matrix.scalar (Fin 2) (b : A) := rfl

/-- Scalar matrices commute with uniform quaternion multiplication. -/
theorem scalarSL_uniform_commute (g : Matrix.SpecialLinearGroup (Fin 2) R) (b : Aˣ) :
    Commute (scalarSL (A := A) g) (uniform b) := by
  apply Units.ext
  change (scalarSL (A := A) g : Matrix (Fin 2) (Fin 2) A) * Matrix.scalar (Fin 2) (b : A) =
    Matrix.scalar (Fin 2) (b : A) * (scalarSL (A := A) g : Matrix (Fin 2) (Fin 2) A)
  ext i j
  simp only [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, scalarSL_apply]
  exact Algebra.commutes (g i j) (b : A)

/-- The commuting product before the coordinate change. -/
def product : Matrix.SpecialLinearGroup (Fin 2) R × Aˣ →*
    (Matrix (Fin 2) (Fin 2) A)ˣ :=
  (scalarSL (R := R) (A := A)).noncommCoprod uniform scalarSL_uniform_commute

@[simp] theorem product_apply (g : Matrix.SpecialLinearGroup (Fin 2) R) (b : Aˣ)
    (i j : Fin 2) :
    (product (g, b) : Matrix (Fin 2) (Fin 2) A) i j =
      algebraMap R A (g i j) * (b : A) := by
  change ((scalarSL (A := A) g : Matrix (Fin 2) (Fin 2) A) * Matrix.scalar (Fin 2) (b : A)) i j = _
  simp only [Matrix.scalar_apply, Matrix.mul_diagonal, scalarSL_apply]

/-- The row-coordinate change `(x,y) ↦ (x,yℓ⁻¹)`. -/
def coordinateChange (l : Aˣ) : (Matrix (Fin 2) (Fin 2) A)ˣ where
  val := !![1, 0; 0, (l⁻¹ : Aˣ)]
  inv := !![1, 0; 0, (l : A)]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The product action in the original hyperbolic coordinates. -/
def action (l : Aˣ) : Matrix.SpecialLinearGroup (Fin 2) R × Aˣ →*
    (Matrix (Fin 2) (Fin 2) A)ˣ :=
  (MulAut.conj (coordinateChange l)).toMonoidHom.comp product

@[simp] theorem action_eq_one_iff (l : Aˣ)
    (g : Matrix.SpecialLinearGroup (Fin 2) R) (b : Aˣ) :
    action l (g, b) = 1 ↔ product (g, b) = 1 := by
  change MulAut.conj (coordinateChange l) (product (g, b)) = 1 ↔ _
  exact (MulAut.conj (coordinateChange l)).map_eq_one_iff

/-- The first diagonal entry is unchanged by the coordinate change. -/
@[simp] theorem action_zero_zero (l : Aˣ)
    (g : Matrix.SpecialLinearGroup (Fin 2) R) (b : Aˣ) :
    (action l (g,b) : Matrix (Fin 2) (Fin 2) A) 0 0 = algebraMap R A (g 0 0) * (b : A) := by
  change (((coordinateChange l : Matrix (Fin 2) (Fin 2) A) * (product (A := A) (g,b)).val) *
    (coordinateChange l).inv) 0 0 = _
  simp [coordinateChange, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

@[simp] theorem action_zero_one (l : Aˣ)
    (g : Matrix.SpecialLinearGroup (Fin 2) R) (b : Aˣ) :
    (action l (g,b) : Matrix (Fin 2) (Fin 2) A) 0 1 =
      algebraMap R A (g 0 1) * (b : A) * (l : A) := by
  change (((coordinateChange l : Matrix (Fin 2) (Fin 2) A) * (product (A := A) (g,b)).val) *
    (coordinateChange l).inv) 0 1 = _
  simp [coordinateChange, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

@[simp] theorem action_one_zero (l : Aˣ)
    (g : Matrix.SpecialLinearGroup (Fin 2) R) (b : Aˣ) :
    (action l (g,b) : Matrix (Fin 2) (Fin 2) A) 1 0 =
      (↑l⁻¹ : A) * (algebraMap R A (g 1 0) * (b : A)) := by
  change (((coordinateChange l : Matrix (Fin 2) (Fin 2) A) * (product (A := A) (g,b)).val) *
    (coordinateChange l).inv) 1 0 = _
  simp [coordinateChange, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

@[simp] theorem action_one_one (l : Aˣ)
    (g : Matrix.SpecialLinearGroup (Fin 2) R) (b : Aˣ) :
    (action l (g,b) : Matrix (Fin 2) (Fin 2) A) 1 1 =
      (↑l⁻¹ : A) * (algebraMap R A (g 1 1) * (b : A)) * (l : A) := by
  change (((coordinateChange l : Matrix (Fin 2) (Fin 2) A) * (product (A := A) (g,b)).val) *
    (coordinateChange l).inv) 1 1 = _
  simp [coordinateChange, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- The exact kernel equation, with the full square-root-of-one condition on the
coefficient ring rather than just its field-valued signs. -/
theorem product_eq_one_iff (hinj : Function.Injective (algebraMap R A))
    (g : Matrix.SpecialLinearGroup (Fin 2) R) (b : Aˣ) :
    product (g,b) = 1 ↔ ∃ r : R, r * r = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) R) = Matrix.scalar (Fin 2) r ∧
      (b : A) = algebraMap R A r := by
  constructor
  · intro h
    have he (i j : Fin 2) := congrArg (fun z : (Matrix (Fin 2) (Fin 2) A)ˣ =>
      (z : Matrix (Fin 2) (Fin 2) A) i j) h
    simp only [product_apply, Units.val_one, Matrix.one_apply] at he
    have h00 : algebraMap R A (g 0 0) = (b⁻¹ : Aˣ) := by
      have h := congrArg (fun z : A => z * (b⁻¹ : Aˣ)) (he 0 0)
      simpa [mul_assoc] using h
    have h11 : algebraMap R A (g 1 1) = (b⁻¹ : Aˣ) := by
      have h := congrArg (fun z : A => z * (b⁻¹ : Aˣ)) (he 1 1)
      simpa [mul_assoc] using h
    have h01 : g 0 1 = 0 := by
      apply hinj
      have h := congrArg (fun z : A => z * (b⁻¹ : Aˣ)) (he 0 1)
      simpa [mul_assoc] using h
    have h10 : g 1 0 = 0 := by
      apply hinj
      have h := congrArg (fun z : A => z * (b⁻¹ : Aˣ)) (he 1 0)
      simpa [mul_assoc] using h
    have hdiag : g 1 1 = g 0 0 := hinj (h11.trans h00.symm)
    have hg : (g : Matrix (Fin 2) (Fin 2) R) = Matrix.scalar (Fin 2) (g 0 0) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, h01, h10, hdiag]
    have hrr : g 0 0 * g 0 0 = 1 := by
      have hd := g.property
      rw [Matrix.det_fin_two, h01, h10, hdiag] at hd
      simpa using hd
    refine ⟨g 0 0, hrr, hg, ?_⟩
    have hrrA : algebraMap R A (g 0 0) * algebraMap R A (g 0 0) = 1 := by
      rw [← _root_.map_mul, hrr, _root_.map_one]
    calc
      (b : A) = 1 * (b : A) := (one_mul _).symm
      _ = (algebraMap R A (g 0 0) * algebraMap R A (g 0 0)) * (b : A) := by rw [hrrA]
      _ = algebraMap R A (g 0 0) := by rw [mul_assoc, h00]; simp
  · rintro ⟨r, hrr, hg, hb⟩
    apply Units.ext
    ext i j
    rw [product_apply, hg]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.scalar_apply, hb, ← _root_.map_mul, hrr]

/-- The coordinate change preserves the exact diagonal square-root-of-one kernel. -/
theorem action_kernel (hinj : Function.Injective (algebraMap R A)) (l : Aˣ)
    (g : Matrix.SpecialLinearGroup (Fin 2) R) (b : Aˣ) :
    action l (g,b) = 1 ↔ ∃ r : R, r * r = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) R) = Matrix.scalar (Fin 2) r ∧
      (b : A) = algebraMap R A r := by
  rw [action_eq_one_iff, product_eq_one_iff hinj]

/-- Sandwiching preserves the actual alternating subspace over any commutative ring. -/
theorem sandwich_mem_alternating
    (σ : FirstKindInvolution R A) {z : A} (hz : z ∈ σ.alternatingSubspace) (a : A) :
    a * z * σ a ∈ σ.alternatingSubspace := by
  obtain ⟨w, rfl⟩ := σ.mem_alternatingSubspace.mp hz
  apply σ.mem_alternatingSubspace.mpr
  refine ⟨a * w * σ a, ?_⟩
  simp only [FirstKindInvolution.map_mul, FirstKindInvolution.apply_apply]
  noncomm_ring

/-- An alternating unit has alternating inverse, including in characteristic two. -/
theorem inverse_mem_alternating (σ : FirstKindInvolution R A) (l : Aˣ)
    (hl : (l : A) ∈ σ.alternatingSubspace) : (↑l⁻¹ : A) ∈ σ.alternatingSubspace := by
  have hs : σ (l : A) = -(l : A) := by
    obtain ⟨w, hw⟩ := σ.mem_alternatingSubspace.mp hl
    rw [← hw]
    simp
  have hi : σ (l⁻¹ : Aˣ) = -(l⁻¹ : Aˣ) := by
    apply (Units.mul_right_inj (-l)).mp
    change -(l : A) * σ (l⁻¹ : Aˣ) = -(l : A) * -(l⁻¹ : Aˣ)
    have h := σ.map_mul (↑l⁻¹ : A) (l : A)
    simp only [Units.inv_mul, FirstKindInvolution.map_one, hs] at h
    simpa only [neg_mul_neg, Units.mul_inv] using h.symm
  have h := (σ.alternatingSubspace).neg_mem (sandwich_mem_alternating σ hl (l⁻¹ : Aˣ))
  simpa only [hi, Units.inv_mul, one_mul, mul_neg, neg_neg] using h

/-- The actual upper-triangular representative of the quaternionic hyperbolic plane. -/
def hyperbolicMatrix : Matrix (Fin 2) (Fin 2) A := !![0,1;0,0]

private theorem scalar_action_entries (l : Aˣ) (g : Matrix.SpecialLinearGroup (Fin 2) R) :
    (action l (g,1) : Matrix (Fin 2) (Fin 2) A) =
      !![algebraMap R A (g 0 0), g 0 1 • (l : A);
        g 1 0 • (l⁻¹ : Aˣ), algebraMap R A (g 1 1)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Algebra.smul_def, mul_assoc, ← Algebra.commutes]

/-- A scalar special-linear matrix preserves the actual hyperbolic quadratic class. -/
theorem scalar_preserves (σ : FirstKindInvolution R A) (l : Aˣ)
    (hl : (l : A) ∈ σ.alternatingSubspace)
    (g : Matrix.SpecialLinearGroup (Fin 2) R) :
    (action l (g,1) : Matrix (Fin 2) (Fin 2) A) * hyperbolicMatrix *
        σ.matrix (Fin 2) (action l (g,1) : Matrix (Fin 2) (Fin 2) A) - hyperbolicMatrix ∈
      (σ.matrix (Fin 2)).alternatingSubspace := by
  have hs : σ (l : A) = -(l : A) := by
    obtain ⟨w, hw⟩ := σ.mem_alternatingSubspace.mp hl
    rw [← hw]
    simp
  have hli := inverse_mem_alternating σ l hl
  have hsi : σ (l⁻¹ : Aˣ) = -(l⁻¹ : Aˣ) := by
    obtain ⟨w, hw⟩ := σ.mem_alternatingSubspace.mp hli
    rw [← hw]
    simp
  have h0 : -(g 0 0 * g 0 1) • (l : A) ∈ σ.alternatingSubspace :=
    σ.alternatingSubspace.smul_mem _ hl
  have h1 : (g 1 0 * g 1 1) • (↑l⁻¹ : A) ∈ σ.alternatingSubspace :=
    σ.alternatingSubspace.smul_mem _ hli
  obtain ⟨w0, hw0⟩ := σ.mem_alternatingSubspace.mp h0
  obtain ⟨w1, hw1⟩ := σ.mem_alternatingSubspace.mp h1
  apply (σ.matrix (Fin 2)).mem_alternatingSubspace.mpr
  refine ⟨!![w0, algebraMap R A (g 0 1 * g 1 0); 0, w1], ?_⟩
  have hd : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.property
  have hd' : g 0 0 * g 1 1 - 1 = g 0 1 * g 1 0 := by
    linear_combination hd
  rw [scalar_action_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [FirstKindInvolution.matrix_apply, hyperbolicMatrix,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two, hs, hsi, hw0, hw1,
      ← Algebra.algebraMap_eq_smul_one, ← _root_.map_mul]
  · simp [Algebra.smul_def, ← mul_assoc, ← _root_.map_mul, mul_comm]
  · rw [← _root_.map_one (algebraMap R A), ← _root_.map_sub, hd']
  · rw [Algebra.smul_def, ← _root_.map_mul]
  · simp only [Algebra.smul_def]
    rw [← Algebra.commutes (g 1 1) (↑l⁻¹ : A), ← mul_assoc, ← _root_.map_mul]

/-- A norm-one uniform factor preserves the chosen hyperbolic representative exactly. -/
theorem uniform_preserves (σ : FirstKindInvolution R A) (l : Aˣ)
    (hl : (l : A) ∈ σ.alternatingSubspace) (b : Aˣ)
    (hb : (b : A) * (l : A) * σ (b : A) = (l : A)) :
    (action (R := R) l (1,b) : Matrix (Fin 2) (Fin 2) A) * hyperbolicMatrix *
      σ.matrix (Fin 2) (action (R := R) l (1,b) : Matrix (Fin 2) (Fin 2) A) = hyperbolicMatrix := by
  have hs : σ (l : A) = -(l : A) := by
    obtain ⟨w, hw⟩ := σ.mem_alternatingSubspace.mp hl
    rw [← hw]
    simp
  have hsi : σ (l⁻¹ : Aˣ) = -(l⁻¹ : Aˣ) := by
    obtain ⟨w, hw⟩ := σ.mem_alternatingSubspace.mp (inverse_mem_alternating σ l hl)
    rw [← hw]
    simp
  have hm : (action (R := R) l (1,b) : Matrix (Fin 2) (Fin 2) A) =
      !![(b : A),0; 0,(↑l⁻¹ : A) * (b : A) * (l : A)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have h := congrArg (fun z : A => z * (l⁻¹ : Aˣ)) hb
  have he : (b : A) * ((l : A) * (σ (b : A) * (l⁻¹ : Aˣ))) = 1 := by
    simpa only [mul_assoc, Units.mul_inv] using h
  rw [hm]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hyperbolicMatrix, FirstKindInvolution.matrix_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, hs, hsi, mul_assoc, he]

/-- The full commuting product preserves the hyperbolic quadratic class. -/
theorem action_preserves (σ : FirstKindInvolution R A) (l : Aˣ)
    (hl : (l : A) ∈ σ.alternatingSubspace)
    (g : Matrix.SpecialLinearGroup (Fin 2) R) (b : Aˣ)
    (hb : (b : A) * (l : A) * σ (b : A) = (l : A)) :
    (action l (g,b) : Matrix (Fin 2) (Fin 2) A) * hyperbolicMatrix *
        σ.matrix (Fin 2) (action l (g,b) : Matrix (Fin 2) (Fin 2) A) - hyperbolicMatrix ∈
      (σ.matrix (Fin 2)).alternatingSubspace := by
  have hprod : action l (g,b) = action l (g,1) * action (R := R) l (1,b) := by
    rw [← _root_.map_mul]
    simp
  rw [hprod, Units.val_mul, (σ.matrix (Fin 2)).map_mul]
  have hp := uniform_preserves σ l hl b hb
  have he :
      (action l (g,1) : Matrix (Fin 2) (Fin 2) A) *
          (action (R := R) l (1,b) : Matrix (Fin 2) (Fin 2) A) * hyperbolicMatrix *
        (σ.matrix (Fin 2) (action (R := R) l (1,b) : Matrix (Fin 2) (Fin 2) A) *
          σ.matrix (Fin 2) (action l (g,1) : Matrix (Fin 2) (Fin 2) A)) =
      (action l (g,1) : Matrix (Fin 2) (Fin 2) A) * hyperbolicMatrix *
          σ.matrix (Fin 2) (action l (g,1) : Matrix (Fin 2) (Fin 2) A) := by
    calc
      _ = (action l (g,1) : Matrix (Fin 2) (Fin 2) A) *
          ((action (R := R) l (1,b) : Matrix (Fin 2) (Fin 2) A) * hyperbolicMatrix *
            σ.matrix (Fin 2) (action (R := R) l (1,b) : Matrix (Fin 2) (Fin 2) A)) *
          σ.matrix (Fin 2) (action l (g,1) : Matrix (Fin 2) (Fin 2) A) := by
            simp only [Matrix.mul_assoc]
      _ = _ := by rw [hp]
  rw [he]
  exact scalar_preserves σ l hl g

/-- The action respects arbitrary compatible coefficient-ring maps. -/
theorem action_naturality {S B : Type*} [CommRing S] [Ring B] [Algebra S B]
    (f : R →+* S) (F : A →+* B)
    (hF : ∀ r, F (algebraMap R A r) = algebraMap S B (f r))
    (l : Aˣ) (g : Matrix.SpecialLinearGroup (Fin 2) R) (b : Aˣ) :
    (action (Units.map F.toMonoidHom l)
      (Matrix.SpecialLinearGroup.map f g, Units.map F.toMonoidHom b) :
        Matrix (Fin 2) (Fin 2) B) =
      (action l (g,b) : Matrix (Fin 2) (Fin 2) A).map F := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hF]

end Langlands.GroupScheme.Quaternionic.BinaryAction


namespace Langlands.GroupScheme.Quaternionic.BinaryAction

open scoped TensorProduct

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
  (σ : FirstKindInvolution K D)
  (hdim : Module.finrank K D = 4) (hsym : Module.finrank K σ.symmetricSubspace = 3)

/-- The chosen alternating unit in the actual coefficient tensor algebra. -/
def tensorAlternatingUnit (R : Type u) [CommRing R] [Algebra K R] : (R ⊗[K] D)ˣ :=
  Units.map Algebra.TensorProduct.includeRight.toMonoidHom
    (σ.quaternionAlternatingUnit hdim hsym)

omit [Algebra.IsCentral K D] in
@[simp] theorem tensorAlternatingUnit_val (R : Type u) [CommRing R] [Algebra K R] :
    (tensorAlternatingUnit σ hdim hsym R : R ⊗[K] D) =
      1 ⊗ₜ[K] (σ.quaternionAlternatingUnit hdim hsym : D) := rfl

omit [Algebra.IsCentral K D] in
@[simp] theorem tensorAlternatingUnit_inv_val (R : Type u) [CommRing R] [Algebra K R] :
    (↑(tensorAlternatingUnit σ hdim hsym R)⁻¹ : R ⊗[K] D) =
      1 ⊗ₜ[K] (↑(σ.quaternionAlternatingUnit hdim hsym)⁻¹ : D) := rfl

omit [Algebra.IsCentral K D] in
/-- The chosen unit remains alternating over every coefficient algebra. -/
theorem tensorAlternatingUnit_mem (R : Type u) [CommRing R] [Algebra K R] :
    (tensorAlternatingUnit σ hdim hsym R : R ⊗[K] D) ∈
      (σ.baseChange R).alternatingSubspace := by
  obtain ⟨w, hw⟩ := σ.mem_alternatingSubspace.mp
    (σ.quaternionAlternatingUnit_mem hdim hsym)
  apply (σ.baseChange R).mem_alternatingSubspace.mpr
  refine ⟨1 ⊗ₜ[K] w, ?_⟩
  rw [σ.baseChange_tmul, ← TensorProduct.tmul_sub, hw]
  rfl

omit [Algebra.IsCentral K D] in
/-- The actual quaternion conjugation is the same conjugation by the extended unit. -/
theorem quaternionConjugation_baseChange (R : Type u) [CommRing R] [Algebra K R]
    (x : R ⊗[K] D) :
    (σ.quaternionConjugation hdim hsym).baseChange R x =
      (tensorAlternatingUnit σ hdim hsym R : R ⊗[K] D) * σ.baseChange R x *
        (↑(tensorAlternatingUnit σ hdim hsym R)⁻¹ : R ⊗[K] D) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [FirstKindInvolution.map_add, hx, hy, mul_add, add_mul]
  | tmul r a =>
    simp only [FirstKindInvolution.baseChange_tmul, tensorAlternatingUnit_val,
      tensorAlternatingUnit_inv_val, FirstKindInvolution.quaternionConjugation,
      FirstKindInvolution.alternatingTwist_apply, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, mul_one, Units.val_inv_eq_inv_val]

/-- The actual tensor action restricted to the canonical reduced-norm-one units. -/
def normOneAction (R : Type u) [CommRing R] [Algebra K R] :
    Matrix.SpecialLinearGroup (Fin 2) R × Langlands.CentralSimple.reducedNormOne K D R →*
      (Matrix (Fin 2) (Fin 2) (R ⊗[K] D))ˣ :=
  (action (tensorAlternatingUnit σ hdim hsym R)).comp
    ((MonoidHom.id _).prodMap (Langlands.CentralSimple.reducedNormOne K D R).subtype)

omit [FiniteDimensional K D] [Algebra.IsCentral K D] in
/-- Scalars inject into the actual tensor coefficient algebra, also for the zero algebra. -/
theorem tensorScalar_injective (R : Type u) [CommRing R] [Algebra K R] :
    Function.Injective (algebraMap R (R ⊗[K] D)) :=
  Algebra.TensorProduct.includeLeft_injective (R := K) (A := R) (B := D) (S := R)
    (FaithfulSMul.algebraMap_injective K D)

/-- All coefficient-ring points of the product action have exactly the diagonal μ₂ kernel. -/
theorem normOneAction_kernel (R : Type u) [CommRing R] [Algebra K R]
    (g : Matrix.SpecialLinearGroup (Fin 2) R)
    (b : Langlands.CentralSimple.reducedNormOne K D R) :
    normOneAction σ hdim hsym R (g,b) = 1 ↔ ∃ r : R, r * r = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) R) = Matrix.scalar (Fin 2) r ∧
      (b.val : R ⊗[K] D) = algebraMap R (R ⊗[K] D) r :=
  action_kernel (tensorScalar_injective R) (tensorAlternatingUnit σ hdim hsym R) g b.val

variable [Infinite K]

/-- The actual norm-one equation supplies the sandwich identity over every algebra. -/
theorem normOne_sandwich (R : Type u) [CommRing R] [Algebra K R]
    (b : Langlands.CentralSimple.reducedNormOne K D R) :
    (b.val : R ⊗[K] D) * (tensorAlternatingUnit σ hdim hsym R : R ⊗[K] D) *
        σ.baseChange R (b.val : R ⊗[K] D) =
      (tensorAlternatingUnit σ hdim hsym R : R ⊗[K] D) := by
  have h := σ.quaternionConjugation_norm_baseChange hdim hsym R (b.val : R ⊗[K] D)
  rw [quaternionConjugation_baseChange] at h
  have hn := (Langlands.CentralSimple.mem_reducedNormOne K D R b.val).mp b.property
  rw [hn, _root_.map_one] at h
  have he := congrArg (fun z : R ⊗[K] D =>
    z * (tensorAlternatingUnit σ hdim hsym R : R ⊗[K] D)) h
  simpa only [mul_assoc, Units.inv_mul, mul_one, one_mul] using he

/-- The tensor product action really preserves the original hyperbolic quadratic class. -/
theorem normOneAction_preserves (R : Type u) [CommRing R] [Algebra K R]
    (g : Matrix.SpecialLinearGroup (Fin 2) R)
    (b : Langlands.CentralSimple.reducedNormOne K D R) :
    (normOneAction σ hdim hsym R (g,b) : Matrix (Fin 2) (Fin 2) (R ⊗[K] D)) *
        hyperbolicMatrix * (σ.baseChange R).matrix (Fin 2)
          (normOneAction σ hdim hsym R (g,b) : Matrix (Fin 2) (Fin 2) (R ⊗[K] D)) -
            hyperbolicMatrix ∈ ((σ.baseChange R).matrix (Fin 2)).alternatingSubspace :=
  action_preserves (σ.baseChange R) (tensorAlternatingUnit σ hdim hsym R)
    (tensorAlternatingUnit_mem σ hdim hsym R) g b.val
    (normOne_sandwich σ hdim hsym R b)

end Langlands.GroupScheme.Quaternionic.BinaryAction
