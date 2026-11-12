import Langlands.GroupScheme.Quaternionic.BinaryQuaternionAction
import Langlands.GroupScheme.Quaternionic.NormSquareCover
import Langlands.GroupScheme.SpecialLinearBinaryDiagonal

/-! # The norm-square torus in the hyperbolic product action -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v

open scoped Matrix TensorProduct

namespace Langlands.GroupScheme.Quaternionic.BinaryAction

section Ring

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

/-- The actual hyperbolic Levi action of an algebra unit. -/
def hyperbolicLevi (σ : FirstKindInvolution R A) :
    Aˣ →* (Matrix (Fin 2) (Fin 2) A)ˣ where
  toFun a :=
    { val := !![(a : A),0;0,σ (a⁻¹ : Aˣ)]
      inv := !![(a⁻¹ : Aˣ),0;0,σ (a : A)]
      val_inv := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, ← σ.map_mul]
      inv_val := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, ← σ.map_mul] }
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, mul_inv_rev]

@[simp] theorem hyperbolicLevi_zero_zero (σ : FirstKindInvolution R A) (a : Aˣ) :
    (hyperbolicLevi σ a : Matrix (Fin 2) (Fin 2) A) 0 0 = (a : A) := rfl

/-- The standard scalar torus in SL₂ with first diagonal coordinate `t`. -/
def diagonalSL : Rˣ →* Matrix.SpecialLinearGroup (Fin 2) R :=
  SpecialLinear.BinaryUpper.diagonalMatrixHom.comp invMonoidHom

@[simp] theorem diagonalSL_val (t : Rˣ) :
    (diagonalSL t : Matrix (Fin 2) (Fin 2) R) = !![(t : R),0;0,(t⁻¹ : Rˣ)] := by
  simp [diagonalSL, SpecialLinear.BinaryUpper.diagonalMatrixHom,
    SpecialLinear.BinaryUpper.diagonalMatrix]

/-- The norm-one factor's inverse-conjugation relation gives the standard Levi matrix. -/
theorem diagonal_action_eq_levi (σ : FirstKindInvolution R A) (l b : Aˣ)
    (hb : σ (b⁻¹ : Aˣ) = (↑l⁻¹ : A) * (b : A) * (l : A)) (t : Rˣ) :
    action l (diagonalSL t,b) =
      hyperbolicLevi σ ((Units.map (algebraMap R A).toMonoidHom t) * b) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalSL_val, hyperbolicLevi, hb, mul_inv_rev, mul_assoc, ← Algebra.commutes]
  rw [← mul_assoc, ← Algebra.commutes (↑t⁻¹ : R) (↑l⁻¹ : A), mul_assoc]

/-- Vanishing of the off-diagonal entries forces the original SL₂ point into its torus. -/
theorem exists_diagonalSL_of_offDiagonal_eq_zero
    (hinj : Function.Injective (algebraMap R A)) (l b : Aˣ)
    (g : Matrix.SpecialLinearGroup (Fin 2) R)
    (h01 : (action l (g,b) : Matrix (Fin 2) (Fin 2) A) 0 1 = 0)
    (h10 : (action l (g,b) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0) :
    ∃ t : Rˣ, g = diagonalSL t := by
  rw [action_zero_one] at h01
  rw [action_one_zero] at h10
  have hg01 : g 0 1 = 0 := by
    apply hinj
    have he := congrArg (fun z : A => z * (l⁻¹ : Aˣ) * (b⁻¹ : Aˣ)) h01
    simpa [mul_assoc] using he
  have hg10 : g 1 0 = 0 := by
    apply hinj
    have he := congrArg (fun z : A => (l : A) * z * (b⁻¹ : Aˣ)) h10
    simpa [← mul_assoc] using he
  have hd : g 0 0 * g 1 1 = 1 := by
    have h := g.property
    rw [Matrix.det_fin_two, hg01, hg10] at h
    simpa only [mul_zero, sub_zero] using h
  let t : Rˣ := ⟨g 0 0, g 1 1, hd, (mul_comm _ _).trans hd⟩
  refine ⟨t, ?_⟩
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [diagonalSL_val, t, hg01, hg10]

end Ring

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
  (σ : FirstKindInvolution K D)
  (hdim : Module.finrank K D = 4) (hsym : Module.finrank K σ.symmetricSubspace = 3)

/-- An actual norm-square pair determines a point of the diagonal torus times SL₁(D). -/
def normSquareSpinTorus (R : Type u) [CommRing R] [Algebra K R] :
    Langlands.CentralSimple.normSquareCover K D R →*
      Matrix.SpecialLinearGroup (Fin 2) R × Langlands.CentralSimple.reducedNormOne K D R :=
  ((diagonalSL (R := R)).comp (Langlands.CentralSimple.normSquareRoot K D R)).prod
    ((MonoidHom.fst _ _).comp
      (Langlands.CentralSimple.normSquareProductEquiv K D R
        (FirstKindInvolution.reducedDegree_eq_two_of_finrank_four hdim)).symm.toMonoidHom)

@[simp] theorem normSquareSpinTorus_fst (R : Type u) [CommRing R] [Algebra K R]
    (x : Langlands.CentralSimple.normSquareCover K D R) :
    (normSquareSpinTorus hdim R x).1 = diagonalSL x.val.2 := rfl

@[simp] theorem normSquareSpinTorus_snd (R : Type u) [CommRing R] [Algebra K R]
    (x : Langlands.CentralSimple.normSquareCover K D R) :
    (normSquareSpinTorus hdim R x).2 =
      Langlands.CentralSimple.normSquareNormOnePart K D R
        (FirstKindInvolution.reducedDegree_eq_two_of_finrank_four hdim) x := rfl

/-- The explicit norm-one/scalar product enters the two factors with their own coordinates. -/
theorem normSquareSpinTorus_product (R : Type u) [CommRing R] [Algebra K R]
    (b : Langlands.CentralSimple.reducedNormOne K D R) (t : Rˣ) :
    normSquareSpinTorus hdim R
      (Langlands.CentralSimple.normSquareProductEquiv K D R
        (FirstKindInvolution.reducedDegree_eq_two_of_finrank_four hdim) (b,t)) =
      (diagonalSL t,b) := by
  apply Prod.ext
  · simp [normSquareSpinTorus_fst, Langlands.CentralSimple.normSquareProductEquiv]
  · change ((Langlands.CentralSimple.normSquareProductEquiv K D R
      (FirstKindInvolution.reducedDegree_eq_two_of_finrank_four hdim)).symm
        ((Langlands.CentralSimple.normSquareProductEquiv K D R
          (FirstKindInvolution.reducedDegree_eq_two_of_finrank_four hdim)) (b,t))).1 = b
    rw [MulEquiv.symm_apply_apply]

/-- Every product point over a Levi matrix comes from an actual norm-square pair. -/
theorem exists_normSquareSpinTorus_of_eq_levi (R : Type u) [CommRing R] [Algebra K R]
    (g : Matrix.SpecialLinearGroup (Fin 2) R)
    (b : Langlands.CentralSimple.reducedNormOne K D R) (a : (R ⊗[K] D)ˣ)
    (h : normOneAction σ hdim hsym R (g,b) = hyperbolicLevi (σ.baseChange R) a) :
    ∃ x : Langlands.CentralSimple.normSquareCover K D R,
      x.val.1 = a ∧ normSquareSpinTorus hdim R x = (g,b) := by
  have he (i j : Fin 2) := congrArg
    (fun z : (Matrix (Fin 2) (Fin 2) (R ⊗[K] D))ˣ =>
      (z : Matrix (Fin 2) (Fin 2) (R ⊗[K] D)) i j) h
  have h01 : (action (tensorAlternatingUnit σ hdim hsym R) (g,b.val) :
      Matrix (Fin 2) (Fin 2) (R ⊗[K] D)) 0 1 = 0 := he 0 1
  have h10 : (action (tensorAlternatingUnit σ hdim hsym R) (g,b.val) :
      Matrix (Fin 2) (Fin 2) (R ⊗[K] D)) 1 0 = 0 := he 1 0
  obtain ⟨t, ht⟩ := exists_diagonalSL_of_offDiagonal_eq_zero (tensorScalar_injective R)
    (tensorAlternatingUnit σ hdim hsym R) b.val g h01 h10
  let x := Langlands.CentralSimple.normSquareProductEquiv K D R
    (FirstKindInvolution.reducedDegree_eq_two_of_finrank_four hdim) (b,t)
  refine ⟨x, ?_, ?_⟩
  · apply Units.ext
    have h00 := he 0 0
    change (action (tensorAlternatingUnit σ hdim hsym R) (g,b.val) :
      Matrix (Fin 2) (Fin 2) (R ⊗[K] D)) 0 0 = (a : R ⊗[K] D) at h00
    rw [action_zero_zero, ht] at h00
    have hc := Langlands.CentralSimple.normCoverScalarUnits_commute K D R t b.val
    change ((b.val * Langlands.CentralSimple.normCoverScalarUnits K D R t :
      (R ⊗[K] D)ˣ) : R ⊗[K] D) = _
    rw [← hc.eq]
    simpa [diagonalSL_val] using h00
  · rw [normSquareSpinTorus_product, ← ht]

/-- In the actual product model the hyperbolic Levi obstruction is exactly a square norm. -/
theorem norm_square_of_normOneAction_eq_levi (R : Type u) [CommRing R] [Algebra K R]
    (g : Matrix.SpecialLinearGroup (Fin 2) R)
    (b : Langlands.CentralSimple.reducedNormOne K D R) (a : (R ⊗[K] D)ˣ)
    (h : normOneAction σ hdim hsym R (g,b) = hyperbolicLevi (σ.baseChange R) a) :
    ∃ t : Rˣ, Langlands.CentralSimple.reducedNormUnits K D R a = t ^ 2 := by
  obtain ⟨x, hx, _⟩ := exists_normSquareSpinTorus_of_eq_levi σ hdim hsym R g b a h
  exact ⟨x.val.2, hx ▸ x.property⟩

variable [Infinite K]

/-- The inverse in SL₁(D) satisfies the required conjugation relation over every algebra. -/
theorem normOne_conjugate_inv (R : Type u) [CommRing R] [Algebra K R]
    (b : Langlands.CentralSimple.reducedNormOne K D R) :
    σ.baseChange R (↑b.val⁻¹ : R ⊗[K] D) =
      (↑(tensorAlternatingUnit σ hdim hsym R)⁻¹ : R ⊗[K] D) *
        (b.val : R ⊗[K] D) * (tensorAlternatingUnit σ hdim hsym R : R ⊗[K] D) := by
  have h := normOne_sandwich σ hdim hsym R b⁻¹
  have he := congrArg (fun z : R ⊗[K] D =>
    (↑(tensorAlternatingUnit σ hdim hsym R)⁻¹ : R ⊗[K] D) * (b.val : R ⊗[K] D) * z) h
  simpa only [Subgroup.coe_inv, ← mul_assoc, Units.mul_inv_cancel_right,
    Units.inv_mul, one_mul] using he

/-- The diagonal restriction of the product action is exactly the norm-square Levi cover. -/
theorem normSquareSpinTorus_action (R : Type u) [CommRing R] [Algebra K R]
    (x : Langlands.CentralSimple.normSquareCover K D R) :
    normOneAction σ hdim hsym R (normSquareSpinTorus hdim R x) =
      hyperbolicLevi (σ.baseChange R) x.val.1 := by
  let b := Langlands.CentralSimple.normSquareNormOnePart K D R
    (FirstKindInvolution.reducedDegree_eq_two_of_finrank_four hdim) x
  change action (tensorAlternatingUnit σ hdim hsym R) (diagonalSL x.val.2, b.val) = _
  rw [diagonal_action_eq_levi (σ.baseChange R) _ b.val
    (normOne_conjugate_inv σ hdim hsym R b) x.val.2]
  have he := congrArg (fun z : Langlands.CentralSimple.normSquareCover K D R => z.val.1)
    ((Langlands.CentralSimple.normSquareProductEquiv K D R
      (FirstKindInvolution.reducedDegree_eq_two_of_finrank_four hdim)).apply_symm_apply x)
  change b.val * Langlands.CentralSimple.normCoverScalarUnits K D R x.val.2 = x.val.1 at he
  have hc := Langlands.CentralSimple.normCoverScalarUnits_commute K D R x.val.2 b.val
  change hyperbolicLevi (σ.baseChange R)
    (Langlands.CentralSimple.normCoverScalarUnits K D R x.val.2 * b.val) = _
  rw [hc.eq, he]

end Langlands.GroupScheme.Quaternionic.BinaryAction
