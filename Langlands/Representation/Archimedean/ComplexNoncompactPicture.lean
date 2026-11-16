import Langlands.Representation.Archimedean.ComplexDuality.LieInvariance
import Langlands.Representation.Archimedean.ComplexLowerUnipotentRestriction
import Langlands.Representation.Archimedean.RealPolynomialMatrices

/-!
# The noncompact picture: right derivatives on the lower unipotent group

Coordinates `v : Lw n → ℂ` (indexed by the positions strictly below the diagonal) parametrize
the lower unipotent matrices `nbMat v`. For a function `f` of a smooth principal series
transforming under the diagonal torus by a character with derivative `Λ`, the right derivative
along `X` at `nbMat v` is (`rightDerivative_nbMat`)
`(R(X) f)(nbMat v) = Λ(diag Y) f(nbMat v) + D(f ∘ nbMat)(v)[W v]`,
where `Y = nbMat v · X · (nbMat v)⁻¹`, and `W v` are the coordinates of the strictly lower part
of `Y` times `nbMat v`. The upper part of `Y` contributes nothing because `f` is invariant
under the upper unipotent group. `Y` and `W` are polynomial in `(v, v̄)`.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator ComplexConjugate ContDiff Manifold

set_option autoImplicit false

namespace Langlands.Archimedean.NoncompactPicture

open Langlands.GeneralLinear Langlands.Archimedean.RealPolynomialFunctions

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

/-- Positions strictly below the diagonal. -/
abbrev Lw (n : ℕ) := {p : Fin n × Fin n // p.2 < p.1}

/-- The strictly lower triangular matrix with entries `w`. -/
def lowMat (w : Lw n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => if h : b < a then w ⟨(a, b), h⟩ else 0

/-- The lower unipotent matrix `1 + lowMat v`. -/
def nbMat (v : Lw n → ℂ) : Matrix (Fin n) (Fin n) ℂ := 1 + lowMat v

/-- The coordinates of the strictly lower part of a matrix. -/
def lowCoords (M : Matrix (Fin n) (Fin n) ℂ) : Lw n → ℂ := fun p => M p.1.1 p.1.2

theorem lowMat_add (v w : Lw n → ℂ) : lowMat (v + w) = lowMat v + lowMat w := by
  ext a b; simp only [lowMat, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]; split_ifs <;> simp

theorem lowMat_smul (c : ℝ) (w : Lw n → ℂ) : lowMat (c • w) = c • lowMat w := by
  ext a b; simp only [lowMat, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply]; split_ifs <;> simp

/-- `lowMat` as a real-linear map. -/
def lowMatCLM : (Lw n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := lowMat
      map_add' := lowMat_add
      map_smul' := lowMat_smul }

theorem nbMat_det (v : Lw n → ℂ) : (nbMat v).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · refine Finset.prod_eq_one fun a _ => ?_
    simp [nbMat, lowMat]
  · intro a b hab
    have hab' : a < b := hab
    have hne : a ≠ b := ne_of_lt hab'
    simp only [nbMat, lowMat, Matrix.add_apply, Matrix.one_apply_ne hne, Matrix.of_apply,
      zero_add]
    rw [dite_eq_right (not_lt.2 hab'.le)]

theorem isUnit_nbMat (v : Lw n → ℂ) : IsUnit (nbMat v) := by
  rw [Matrix.isUnit_iff_isUnit_det, nbMat_det]; exact isUnit_one

/-- The lower unipotent element of coordinates `v`. -/
def nbUnit (v : Lw n → ℂ) : Langlands.GeneralLinear n ℂ := (isUnit_nbMat v).unit

@[simp] theorem nbUnit_val (v : Lw n → ℂ) :
    ((nbUnit v : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) = nbMat v := rfl

theorem nbUnit_mem_lowerUnipotent (v : Lw n → ℂ) : nbUnit v ∈ lowerUnipotent n ℂ := by
  refine (mem_lowerUnipotent_iff n ℂ _).2 ⟨fun a b hab => ?_, fun a => ?_⟩
  · simp only [nbUnit_val, nbMat, lowMat, Matrix.add_apply, Matrix.one_apply_ne (ne_of_lt hab),
      Matrix.of_apply, zero_add]
    rw [dite_eq_right (not_lt.2 hab.le)]
  · simp [nbMat, lowMat]

theorem exists_nbUnit_eq {L : Langlands.GeneralLinear n ℂ} (hL : L ∈ lowerUnipotent n ℂ) :
    ∃ v, nbUnit v = L := by
  obtain ⟨hup, hdiag⟩ := (mem_lowerUnipotent_iff n ℂ L).1 hL
  refine ⟨lowCoords (L : Matrix (Fin n) (Fin n) ℂ), Units.ext ?_⟩
  ext a b
  simp only [nbUnit_val, nbMat, lowMat, lowCoords, Matrix.add_apply, Matrix.of_apply]
  rcases lt_trichotomy a b with h | rfl | h
  · rw [Matrix.one_apply_ne (ne_of_lt h), dite_eq_right (not_lt.2 h.le), hup a b h, add_zero]
  · simp [hdiag]
  · rw [Matrix.one_apply_ne (ne_of_gt h), dite_eq_left h, zero_add]

/-! ## Polynomiality -/

theorem isPolyMat_nbMat : IsPolyMat (ι := Lw n) 1 (nbMat (n := n)) := by
  intro a b
  by_cases h : b < a
  · have : (fun v : Lw n → ℂ => nbMat v a b) = coord (Lw n) (⟨(a, b), h⟩, false) := by
      funext v
      simp [nbMat, lowMat, Matrix.one_apply_ne (ne_of_gt h), h, coord]
    rw [this]; exact coord_mem_degLE _
  · have : (fun v : Lw n → ℂ => nbMat v a b) = fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) a b := by
      funext v
      simp [nbMat, lowMat, h]
    rw [this]; exact const_mem_degLE _ 1

theorem nbMat_inv (v : Lw n → ℂ) : (nbMat v)⁻¹ = (nbMat v).adjugate := by
  rw [Matrix.inv_def, nbMat_det, Ring.inverse_one, one_smul]

theorem isPolyMat_nbMat_inv : IsPolyMat (ι := Lw n) n (fun v => (nbMat v)⁻¹) := by
  have := (isPolyMat_nbMat (n := n)).adjugate
  simp only [Fintype.card_fin, mul_one] at this
  intro a b
  simpa [nbMat_inv] using this a b

/-! ## The formula -/

/-- The diagonal, strictly upper and strictly lower parts of a matrix. -/
def diagPart (Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun a => Y a a

def upperPart (Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => if a < b then Y a b else 0

theorem eq_upper_add_diag_add_low (Y : Matrix (Fin n) (Fin n) ℂ) :
    Y = upperPart Y + diagPart Y + lowMat (lowCoords Y) := by
  ext a b
  simp only [upperPart, diagPart, lowMat, lowCoords, Matrix.add_apply, Matrix.of_apply,
    Matrix.diagonal_apply]
  rcases lt_trichotomy a b with h | rfl | h
  · simp [h, ne_of_lt h, not_lt.2 h.le]
  · simp
  · simp [h, ne_of_gt h, not_lt.2 h.le]

/-- **The right derivative in the noncompact picture.** Let `f` be in the principal series of
`χ`, invariant under the upper unipotent group (`principalSeriesCharacter χ 1 = 1`), and let the
torus derivative be `Λ`: `D(unitsExtension f)(y)[diag(d) y] = Λ d · f(y)` at units `y`. Then
`(R(X) f)(nbMat v) = Λ(diag Y) f(nbMat v) + D(f ∘ nbUnit)(v)[W v]`. -/
theorem rightDerivative_nbMat {χ : ℕ → ℂˣ → ℂ} {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : f ∈ principalSeries ℂ n χ) (hχ1 : principalSeriesCharacter ℂ n χ 1 = 1)
    (Λ : (Fin n → ℂ) → ℂ)
    (hΛ : ∀ (d : Fin n → ℂ) (y : Langlands.GeneralLinear n ℂ),
      fderiv ℝ (unitsExtension f) (y : Matrix (Fin n) (Fin n) ℂ)
        (Matrix.diagonal d * (y : Matrix (Fin n) (Fin n) ℂ)) = Λ d * f y)
    (X : Matrix (Fin n) (Fin n) ℂ) (v : Lw n → ℂ) :
    rightDerivative (matrixModel ℂ n) X f (nbUnit v) =
      Λ (fun a => (nbMat v * X * (nbMat v)⁻¹) a a) * f (nbUnit v) +
        fderiv ℝ (fun w => f (nbUnit w)) v
          (lowCoords (lowMat (lowCoords (nbMat v * X * (nbMat v)⁻¹)) * nbMat v)) := by
  have hfs := ((mem_principalSeries_iff ℂ n χ f).1 hf).1
  set Φ := unitsExtension f
  set y := nbMat v
  set Y := y * X * y⁻¹
  have hyX : y * X = Y * y := by
    rw [show Y * y = y * X * (y⁻¹ * y) by simp only [Y, Matrix.mul_assoc],
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_nbMat v)),
      Matrix.mul_one]
  have hd : DifferentiableAt ℝ Φ y := differentiableAt_unitsExtension hfs (isUnit_nbMat v)
  rw [rightDerivative_eq_fderiv hfs]
  change fderiv ℝ Φ y (y * X) = _
  have hY : Y * y = upperPart Y * y + diagPart Y * y + lowMat (lowCoords Y) * y := by
    conv_lhs => rw [eq_upper_add_diag_add_low Y]
    rw [Matrix.add_mul, Matrix.add_mul]
  rw [hyX, hY, map_add, map_add]
  -- upper part
  have hup : fderiv ℝ Φ y (upperPart Y * y) = 0 := by
    refine ComplexDuality.LieInvariance.fderiv_strictUpper_mul_eq_zero hd (fun u => ?_)
      (fun a b hab => ?_)
    · have h := ((mem_principalSeries_iff ℂ n χ f).1 hf).2 1 u (nbUnit v)
      rw [map_one, one_mul, hχ1, one_mul] at h
      show Φ (((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) *
        ((nbUnit v : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)) =
          Φ ((nbUnit v : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)
      rw [← Units.val_mul]
      change unitsExtension f _ = unitsExtension f _
      rw [unitsExtension_val, unitsExtension_val, h]
    · simp [upperPart, not_lt.2 hab]
  -- diagonal part
  have hdiag : fderiv ℝ Φ y (diagPart Y * y) = Λ (fun a => Y a a) * f (nbUnit v) := by
    have := hΛ (fun a => Y a a) (nbUnit v)
    simpa [diagPart] using this
  -- lower part
  have hlow : fderiv ℝ Φ y (lowMat (lowCoords Y) * y) =
      fderiv ℝ (fun w => f (nbUnit w)) v (lowCoords (lowMat (lowCoords Y) * y)) := by
    have hcomp : (fun w => f (nbUnit w)) = Φ ∘ fun w => 1 + lowMatCLM w := by
      funext w
      simp only [Function.comp_apply, Φ]
      rw [show (1 : Matrix (Fin n) (Fin n) ℂ) + lowMatCLM w = (nbUnit w : Matrix _ _ ℂ) from rfl,
        unitsExtension_val]
    have hlin : HasFDerivAt (fun w : Lw n → ℂ => (1 : Matrix (Fin n) (Fin n) ℂ) + lowMatCLM w)
        lowMatCLM v := (lowMatCLM.hasFDerivAt).const_add 1
    rw [hcomp, (hd.hasFDerivAt.comp v hlin).fderiv]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
    congr 1
    -- the product of a strictly lower and a lower unipotent matrix is strictly lower
    ext a b
    simp only [lowMatCLM, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
      lowMat, lowCoords, Matrix.of_apply]
    split_ifs with hab
    · rfl
    · rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hka : k < a
      · have hbk : ¬ b < k := fun h => hab (lt_trans h hka)
        simp only [Matrix.of_apply, dite_eq_left hka]
        have : y k b = 0 := by
          simp only [y, nbMat, lowMat, Matrix.add_apply, Matrix.of_apply]
          have hkb : k ≠ b := fun h => hab (h ▸ hka)
          rw [Matrix.one_apply_ne hkb, dite_eq_right hbk, zero_add]
        rw [this, mul_zero]
      · simp only [Matrix.of_apply, dite_eq_right hka, zero_mul]
  rw [hup, hdiag, hlow, zero_add]

end Langlands.Archimedean.NoncompactPicture
