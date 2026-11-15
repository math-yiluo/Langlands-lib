import Langlands.Global.RankinSelberg.UnequalAnalyticMatrices
import Langlands.Automorphic.CuspidalL2.SiegelCover

/-! # Padding, transpose inverse and the determinant norm on actual adelic points

Facts about the maps `pad`, `iota`, `detNorm`, `detPower` and `dualFunction` of
`Langlands.Global.RankinSelberg.UnequalIntegrals` on the actual adelic points of the general
linear group scheme: continuity, multiplicativity, compatibility with rational points,
`ι ∘ pad = pad ∘ ι`, `|det ι(g)| = |det g|⁻¹`, and `φ̃ = φ ∘ ι` for left `GL_n(F)`-invariant
`φ`. -/

noncomputable section
universe u
set_option autoImplicit false

open NumberField Langlands Langlands.Global
open scoped CategoryTheory.MonObj

namespace Langlands.Global.RankinSelbergGlobal.UnequalAnalytic

section Matrices

variable {R : Type*} [CommRing R]

/-- Padding is continuous. -/
theorem continuous_padGL [TopologicalSpace R] [IsTopologicalRing R] {m n : ℕ} (h : m ≤ n) :
    Continuous (padGL (R := R) h) := by
  have hval : Continuous (fun M : Matrix.GeneralLinearGroup (Fin m) R =>
      ((padGL h M : Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R)) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    by_cases hij : (i : ℕ) < m ∧ (j : ℕ) < m
    · have he : (fun M : Matrix.GeneralLinearGroup (Fin m) R =>
          ((padGL h M : Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) i j) =
          fun M : Matrix.GeneralLinearGroup (Fin m) R =>
            (M : Matrix (Fin m) (Fin m) R) ⟨i, hij.1⟩ ⟨j, hij.2⟩ := by
        funext M
        rw [padGL_apply, dite_eq_left hij]
      rw [he]
      exact (continuous_apply _).comp
        (Matrix.GeneralLinearGroup.continuous_apply _ continuous_id _)
    · have he : (fun M : Matrix.GeneralLinearGroup (Fin m) R =>
          ((padGL h M : Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) i j) =
          fun _ => (1 : Matrix (Fin n) (Fin n) R) i j := by
        funext M
        rw [padGL_apply, dite_eq_right hij]
      rw [he]
      exact continuous_const
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  have he : (fun M : Matrix.GeneralLinearGroup (Fin m) R =>
      (((padGL h M)⁻¹ : Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R)) =
      (fun M : Matrix.GeneralLinearGroup (Fin m) R =>
        ((padGL h M : Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R)) ∘
        fun M => M⁻¹ := by
    funext M
    simp only [Function.comp_apply, map_inv]
  rw [he]
  exact hval.comp continuous_inv

/-- Transpose inverse commutes with padding. -/
theorem inverseTranspose_padGL {m n : ℕ} (h : m ≤ n) (M : Matrix.GeneralLinearGroup (Fin m) R) :
    GeneralLinear.inverseTranspose n R (padGL h M) =
      padGL h (GeneralLinear.inverseTranspose m R M) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have hinv : (padGL h M)⁻¹ = padGL h M⁻¹ := (map_inv _ _).symm
  simp only [GeneralLinear.inverseTranspose_coe, Matrix.transpose_apply, hinv, padGL_apply]
  by_cases hij : (i : ℕ) < m ∧ (j : ℕ) < m
  · rw [dite_eq_left ⟨hij.2, hij.1⟩, dite_eq_left hij]
  · rw [dite_eq_right (fun h' => hij ⟨h'.2, h'.1⟩), dite_eq_right hij]
    exact congrFun (congrFun (Matrix.transpose_one (n := Fin n) (α := R)) i) j

/-- Transpose inverse commutes with applying a ring homomorphism to the entries. -/
theorem inverseTranspose_map {S : Type*} [CommRing S] (f : R →+* S) {n : ℕ}
    (M : Matrix.GeneralLinearGroup (Fin n) R) :
    GeneralLinear.inverseTranspose n S (Matrix.GeneralLinearGroup.map f M) =
      Matrix.GeneralLinearGroup.map f (GeneralLinear.inverseTranspose n R M) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have hinv : (Matrix.GeneralLinearGroup.map f M)⁻¹ = Matrix.GeneralLinearGroup.map f M⁻¹ :=
    (map_inv _ _).symm
  simp only [GeneralLinear.inverseTranspose_coe, Matrix.transpose_apply, hinv,
    Matrix.GeneralLinearGroup.map_apply]

end Matrices

variable (F : Type u) [Field F] [NumberField F]

local notation "E" => GeneralLinearGroupPoints.adelicEquiv F

/-! ### Padding -/

theorem adelicEquiv_pad {m n : ℕ} (h : m ≤ n) (g : Points F m) :
    E n (pad F h g) = padGL h (E m g) :=
  MulEquiv.apply_symm_apply _ _

theorem pad_mul {m n : ℕ} (h : m ≤ n) (g g' : Points F m) :
    pad F h (g * g') = pad F h g * pad F h g' := by
  simp only [pad, map_mul]

theorem pad_pad {m k n : ℕ} (h₁ : m ≤ k) (h₂ : k ≤ n) (g : Points F m) :
    pad F h₂ (pad F h₁ g) = pad F (h₁.trans h₂) g := by
  simp only [pad, MulEquiv.apply_symm_apply, padGL_padGL]

theorem continuous_pad {m n : ℕ} (h : m ≤ n) : Continuous (pad F h) :=
  (GeneralLinearGroupPoints.adelicHomeomorph F n).symm.continuous.comp
    ((continuous_padGL h).comp (GeneralLinearGroupPoints.adelicHomeomorph F m).continuous)

/-- Padding a rational point gives a rational point. -/
theorem pad_rational {m n : ℕ} (h : m ≤ n) (c : RationalGroupPoints F (Scheme F m)) :
    pad F h (AdelicGroupPoints.rational F (Scheme F m) c) =
      AdelicGroupPoints.rational F (Scheme F n)
        ((GeneralLinearGroupPoints.rationalEquiv F n).symm
          (padGL h (GeneralLinearGroupPoints.rationalEquiv F m c))) := by
  apply (E n).injective
  rw [adelicEquiv_pad, GeneralLinearGroupPoints.adelicEquiv_rational,
    GeneralLinearGroupPoints.adelicEquiv_rational, MulEquiv.apply_symm_apply]
  exact padGL_map _ h _

/-! ### Transpose inverse -/

theorem adelicEquiv_iota {n : ℕ} (g : Points F n) :
    E n (iota F n g) = GeneralLinear.inverseTranspose n (Adeles F) (E n g) :=
  MulEquiv.apply_symm_apply _ _

theorem iota_iota {n : ℕ} (g : Points F n) : iota F n (iota F n g) = g := by
  simp only [iota, MulEquiv.apply_symm_apply, GeneralLinear.inverseTranspose_involutive,
    MulEquiv.symm_apply_apply]

theorem iota_mul {n : ℕ} (g g' : Points F n) :
    iota F n (g * g') = iota F n g * iota F n g' := by
  simp only [iota, map_mul]

theorem continuous_iota (n : ℕ) : Continuous (iota F n) :=
  (GeneralLinearGroupPoints.adelicHomeomorph F n).symm.continuous.comp
    ((GeneralLinear.continuous_inverseTranspose n (Adeles F)).comp
      (GeneralLinearGroupPoints.adelicHomeomorph F n).continuous)

/-- Transpose inverse as a topological group automorphism of the actual adelic points. -/
def iotaEquiv (n : ℕ) : Points F n ≃ₜ* Points F n :=
  ((GeneralLinearGroupPoints.adelicHomeomorph F n).trans
    (GeneralLinear.inverseTransposeContinuous n (Adeles F))).trans
    (GeneralLinearGroupPoints.adelicHomeomorph F n).symm

@[simp]
theorem iotaEquiv_apply (n : ℕ) (g : Points F n) : iotaEquiv F n g = iota F n g := rfl

theorem iota_pad {m n : ℕ} (h : m ≤ n) (g : Points F m) :
    iota F n (pad F h g) = pad F h (iota F m g) := by
  simp only [iota, pad, MulEquiv.apply_symm_apply, inverseTranspose_padGL]

/-- Transpose inverse of a rational point is a rational point. -/
theorem iota_rational {n : ℕ} (c : RationalGroupPoints F (Scheme F n)) :
    iota F n (AdelicGroupPoints.rational F (Scheme F n) c) =
      AdelicGroupPoints.rational F (Scheme F n)
        ((GeneralLinearGroupPoints.rationalEquiv F n).symm
          (GeneralLinear.inverseTranspose n F (GeneralLinearGroupPoints.rationalEquiv F n c))) := by
  apply (E n).injective
  rw [adelicEquiv_iota, GeneralLinearGroupPoints.adelicEquiv_rational,
    GeneralLinearGroupPoints.adelicEquiv_rational, MulEquiv.apply_symm_apply]
  exact inverseTranspose_map _ _

/-- The long Weyl element of `GL_n(𝔸)` is rational. -/
theorem weylLong_eq_rational (n : ℕ) :
    GeneralLinear.weylLong n (Adeles F) = AdelicGL.rational F n (GeneralLinear.weylLong n F) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [AdelicGL.rational_apply, GeneralLinear.weylLong_entry, GeneralLinear.weylLong_entry]
  split_ifs <;> simp

/-- **The dual of an automorphic function is its composition with transpose inverse.** -/
theorem dualFunction_eq {n : ℕ} (φ : Points F n → ℂ)
    (hφ : ∀ (c : RationalGroupPoints F (Scheme F n)) (x : Points F n),
      φ (AdelicGroupPoints.rational F (Scheme F n) c * x) = φ x) (g : Points F n) :
    dualFunction F n φ g = φ (iota F n g) := by
  have hw : (E n).symm (GeneralLinear.weylLong n (Adeles F)) =
      AdelicGroupPoints.rational F (Scheme F n)
        ((GeneralLinearGroupPoints.rationalEquiv F n).symm (GeneralLinear.weylLong n F)) := by
    rw [MulEquiv.symm_apply_eq, GeneralLinearGroupPoints.adelicEquiv_rational,
      MulEquiv.apply_symm_apply, weylLong_eq_rational]
  rw [dualFunction, map_mul, hw]
  exact hφ _ _

theorem dualFunction_iota {n : ℕ} (φ : Points F n → ℂ)
    (hφ : ∀ (c : RationalGroupPoints F (Scheme F n)) (x : Points F n),
      φ (AdelicGroupPoints.rational F (Scheme F n) c * x) = φ x) (g : Points F n) :
    dualFunction F n φ (iota F n g) = φ g := by
  rw [dualFunction_eq F φ hφ, iota_iota]

/-! ### The determinant norm -/

theorem detNorm_eq_absDet {n : ℕ} (g : Points F n) : detNorm F n g = absDet F n (E n g) := rfl

theorem detNorm_pos {n : ℕ} (g : Points F n) : 0 < detNorm F n g := absDet_pos F n _

theorem continuous_detNorm (n : ℕ) : Continuous (detNorm F n) :=
  (continuous_absDet F n).comp (GeneralLinearGroupPoints.adelicHomeomorph F n).continuous

theorem detNorm_mul {n : ℕ} (g g' : Points F n) :
    detNorm F n (g * g') = detNorm F n g * detNorm F n g' := by
  rw [detNorm_eq_absDet, map_mul, absDet_mul]
  rfl

theorem detNorm_rational_mul {n : ℕ} (c : RationalGroupPoints F (Scheme F n)) (g : Points F n) :
    detNorm F n (AdelicGroupPoints.rational F (Scheme F n) c * g) = detNorm F n g := by
  rw [detNorm_eq_absDet, detNorm_eq_absDet, map_mul,
    GeneralLinearGroupPoints.adelicEquiv_rational, absDet_rational_mul]

theorem determinant_padGL {m n : ℕ} (h : m ≤ n) (M : AdelicGL F m) :
    AdelicGL.determinant F n (padGL h M) = AdelicGL.determinant F m M := by
  apply Units.ext
  exact det_padGL h M

theorem detNorm_pad {m n : ℕ} (h : m ≤ n) (g : Points F m) :
    detNorm F n (pad F h g) = detNorm F m g := by
  rw [detNorm_eq_absDet, detNorm_eq_absDet, adelicEquiv_pad]
  simp only [absDet, determinant_padGL]

theorem determinant_inverseTranspose {n : ℕ} (M : AdelicGL F n) :
    AdelicGL.determinant F n (GeneralLinear.inverseTranspose n (Adeles F) M) =
      (AdelicGL.determinant F n M)⁻¹ := by
  rw [← map_inv]
  apply Units.ext
  exact Matrix.det_transpose (((M⁻¹ : AdelicGL F n)) : Matrix (Fin n) (Fin n) (Adeles F))

theorem detNorm_iota {n : ℕ} (g : Points F n) : detNorm F n (iota F n g) = (detNorm F n g)⁻¹ := by
  rw [detNorm_eq_absDet, detNorm_eq_absDet, adelicEquiv_iota]
  simp only [absDet, determinant_inverseTranspose, map_inv, Units.val_inv_eq_inv_val,
    NNReal.coe_inv]

/-! ### Complex powers of the determinant norm -/

theorem norm_detPower {n : ℕ} (g : Points F n) (s : ℂ) :
    ‖detPower F n g s‖ = Real.exp (s.re * Real.log (detNorm F n g)) := by
  rw [detPower, Complex.norm_exp]
  congr 1
  simp

theorem detPower_pad {m n : ℕ} (h : m ≤ n) (g : Points F m) (s : ℂ) :
    detPower F n (pad F h g) s = detPower F m g s := by
  rw [detPower, detPower, detNorm_pad]

theorem detPower_rational_mul {n : ℕ} (c : RationalGroupPoints F (Scheme F n)) (g : Points F n)
    (s : ℂ) :
    detPower F n (AdelicGroupPoints.rational F (Scheme F n) c * g) s = detPower F n g s := by
  rw [detPower, detPower, detNorm_rational_mul]

theorem detPower_iota {n : ℕ} (g : Points F n) (s : ℂ) :
    detPower F n (iota F n g) s = detPower F n g (-s) := by
  rw [detPower, detPower, detNorm_iota, Real.log_inv]
  congr 1
  push_cast
  ring

theorem continuous_detPower (n : ℕ) (s : ℂ) : Continuous (fun g : Points F n => detPower F n g s) :=
  Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    ((continuous_detNorm F n).log fun g => (detNorm_pos F g).ne')))

end Langlands.Global.RankinSelbergGlobal.UnequalAnalytic
