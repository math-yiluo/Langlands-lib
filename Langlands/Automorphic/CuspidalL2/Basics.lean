import Langlands.Global.AdelicGLSiegelShape
import Langlands.Automorphic.ConstantTerm
import Langlands.Global.PositiveRealIdeles
import Langlands.Global.ArchimedeanGrowth
import Langlands.Global.AdeleQuotientCompactProof
import Langlands.Group.GL.BlockUnipotent

/-! # Diagonal tori, block unipotents and adelic splittings -/

noncomputable section
universe u
open scoped Classical
open NumberField
set_option autoImplicit false

namespace Langlands.GeneralLinear

variable {R : Type*} [CommRing R] {a b n : ℕ}

/-- Conjugating a block unipotent matrix by an invertible diagonal matrix rescales its block. -/
theorem diagonalGL_inv_mul_blockUnipotent_mul (h : a + b = n) (d : Fin n → Rˣ)
    (X : Matrix (Fin a) (Fin b) R) :
    (Global.PrimitiveAdelicHeight.diagonalGL d)⁻¹ * blockUnipotent h X *
        Global.PrimitiveAdelicHeight.diagonalGL d =
      blockUnipotent h (Matrix.of fun i j =>
        (((d (finSumFinEquiv.trans (finCongr h) (Sum.inl i)))⁻¹ : Rˣ) : R) * X i j *
          (d (finSumFinEquiv.trans (finCongr h) (Sum.inr j)) : R)) := by
  apply Units.ext
  ext k l
  obtain ⟨p, rfl⟩ := (finSumFinEquiv.trans (finCongr h)).surjective k
  obtain ⟨q, rfl⟩ := (finSumFinEquiv.trans (finCongr h)).surjective l
  change (((Matrix.diagonal fun i => (((d i)⁻¹ : Rˣ) : R)) *
    (blockUnipotent h X : Matrix (Fin n) (Fin n) R) * Matrix.diagonal fun i => (d i : R)) :
      Matrix (Fin n) (Fin n) R) _ _ = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, blockUnipotent_val, blockUnipotent_val]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases p with i | i <;> rcases q with j | j
  · by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  · simp
  · simp
  · by_cases hij : i = j
    · subst hij; simp
    · simp [hij]

end Langlands.GeneralLinear

namespace Langlands.Global

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

namespace AdelicGL

theorem ext_infinite_finite {g g' : AdelicGL K n} (h1 : infinite K n g = infinite K n g')
    (h2 : finite K n g = finite K n g') : g = g' := by
  rw [← pair_projections K n g, ← pair_projections K n g', h1, h2]

@[simp]
theorem infinite_ofInfinite (x : InfiniteAdelicGL K n) : infinite K n (ofInfinite K n x) = x := by
  apply Units.ext; rfl

@[simp]
theorem finite_ofInfinite (x : InfiniteAdelicGL K n) : finite K n (ofInfinite K n x) = 1 := by
  apply Units.ext; rfl

@[simp]
theorem infinite_ofFinite (x : FiniteAdelicGL K n) : infinite K n (ofFinite K n x) = 1 := by
  apply Units.ext; rfl

@[simp]
theorem finite_ofFinite (x : FiniteAdelicGL K n) : finite K n (ofFinite K n x) = x := by
  apply Units.ext; rfl

theorem ofInfinite_commute (x : InfiniteAdelicGL K n) (y : FiniteAdelicGL K n) :
    ofInfinite K n x * ofFinite K n y = ofFinite K n y * ofInfinite K n x :=
  ext_infinite_finite K n (by simp) (by simp)

theorem eq_ofInfinite_mul_ofFinite (g : AdelicGL K n) :
    g = ofInfinite K n (infinite K n g) * ofFinite K n (finite K n g) :=
  ext_infinite_finite K n (by simp) (by simp)

/-- An adelic block unipotent matrix is the product of its infinite and finite parts. -/
theorem blockUnipotent_eq {a b : ℕ} (h : a + b = n) (Y : Matrix (Fin a) (Fin b) (Adeles K)) :
    GeneralLinear.blockUnipotent h Y =
      ofInfinite K n (GeneralLinear.blockUnipotent h
          (Y.map (RingHom.fst (InfiniteAdeleRing K) (FiniteAdeles K)))) *
        ofFinite K n (GeneralLinear.blockUnipotent h
          (Y.map (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeles K)))) := by
  refine ext_infinite_finite K n ?_ ?_
  · rw [map_mul, infinite_ofInfinite, infinite_ofFinite, mul_one]
    exact GeneralLinear.map_blockUnipotent _ h Y
  · rw [map_mul, finite_ofInfinite, finite_ofFinite, one_mul]
    exact GeneralLinear.map_blockUnipotent _ h Y

end AdelicGL

/-- `Real.exp` as a positive real unit. -/
def expUnit (x : ℝ) : NNRealˣ :=
  Units.mk0 ⟨Real.exp x, (Real.exp_pos x).le⟩ (by
    intro h
    have := congrArg NNReal.toReal h
    simp only [NNReal.coe_zero] at this
    exact (Real.exp_pos x).ne' this)

@[simp]
theorem coe_expUnit (x : ℝ) : ((expUnit x : NNReal) : ℝ) = Real.exp x := rfl

theorem expUnit_add (x y : ℝ) : expUnit (x + y) = expUnit x * expUnit y := by
  apply Units.ext; apply NNReal.eq; simp [Real.exp_add]

/-- The archimedean diagonal torus element `diag(e^{x_1}, …, e^{x_n})`, inserted equally at
every infinite place. -/
def torInf (x : Fin n → ℝ) : InfiniteAdelicGL K n :=
  PrimitiveAdelicHeight.diagonalGL fun i => PositiveRealIdeles.infinite K (expUnit (x i))

omit [NumberField K] in
theorem positiveRealIdeles_infinite_val (r : NNRealˣ) :
    ((PositiveRealIdeles.infinite K r : (InfiniteAdeles K)ˣ) : InfiniteAdeles K) =
      PositiveRealIdeles.infiniteRealEmbedding K ((r : NNReal) : ℝ) := rfl

omit [NumberField K] in
theorem positiveRealIdeles_infinite_inv_val (r : NNRealˣ) :
    (((PositiveRealIdeles.infinite K r)⁻¹ : (InfiniteAdeles K)ˣ) : InfiniteAdeles K) =
      PositiveRealIdeles.infiniteRealEmbedding K (((r⁻¹ : NNRealˣ) : NNReal) : ℝ) := by
  rw [← map_inv]; rfl

omit [NumberField K] in
theorem torInf_val (x : Fin n → ℝ) :
    (torInf K n x : Matrix (Fin n) (Fin n) (InfiniteAdeles K)) =
      Matrix.diagonal fun i => PositiveRealIdeles.infiniteRealEmbedding K (Real.exp (x i)) := rfl

omit [NumberField K] in
theorem torInf_add (x y : Fin n → ℝ) : torInf K n (x + y) = torInf K n x * torInf K n y := by
  apply Units.ext
  rw [Units.val_mul, torInf_val, torInf_val, torInf_val, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [Pi.add_apply, Real.exp_add, map_mul]

omit [NumberField K] in
@[simp]
theorem torInf_zero : torInf K n 0 = 1 := by
  apply Units.ext
  rw [torInf_val, Units.val_one]
  simp

omit [NumberField K] in
theorem continuous_torInf : Continuous (torInf K n) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun x : Fin n → ℝ => Matrix.diagonal
      fun i => PositiveRealIdeles.infiniteRealEmbedding K (Real.exp (x i))
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.diagonal_apply]
    split_ifs
    · exact (PositiveRealIdeles.continuous_infiniteRealEmbedding K).comp
        (Real.continuous_exp.comp (continuous_apply i))
    · exact continuous_const
  · change Continuous fun x : Fin n → ℝ => Matrix.diagonal fun i =>
      (((PositiveRealIdeles.infinite K (expUnit (x i)))⁻¹ : (InfiniteAdeles K)ˣ) : InfiniteAdeles K)
    simp only [positiveRealIdeles_infinite_inv_val, Units.val_inv_eq_inv_val, NNReal.coe_inv,
      coe_expUnit]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.diagonal_apply]
    split_ifs
    · exact (PositiveRealIdeles.continuous_infiniteRealEmbedding K).comp
        ((Real.continuous_exp.comp (continuous_apply i)).inv₀ fun _ => (Real.exp_pos _).ne')
    · exact continuous_const

omit [NumberField K] in
/-- Conjugating an archimedean block unipotent by the torus rescales the block entries by
`e^{x_j - x_i}`. -/
theorem torInf_inv_mul_blockUnipotent_mul {a b : ℕ} (h : a + b = n) (x : Fin n → ℝ)
    (Y : Matrix (Fin a) (Fin b) (InfiniteAdeles K)) :
    (torInf K n x)⁻¹ * GeneralLinear.blockUnipotent h Y * torInf K n x =
      GeneralLinear.blockUnipotent h (Matrix.of fun i j =>
        PositiveRealIdeles.infiniteRealEmbedding K
          (Real.exp (x (finSumFinEquiv.trans (finCongr h) (Sum.inr j)) -
            x (finSumFinEquiv.trans (finCongr h) (Sum.inl i)))) * Y i j) := by
  rw [torInf, GeneralLinear.diagonalGL_inv_mul_blockUnipotent_mul]
  congr 1
  ext i j
  simp only [Matrix.of_apply, positiveRealIdeles_infinite_inv_val,
    positiveRealIdeles_infinite_val]
  have key (s t : ℝ) (y : InfiniteAdeles K) :
      PositiveRealIdeles.infiniteRealEmbedding K (((expUnit s)⁻¹ : NNRealˣ) : NNReal) * y *
          PositiveRealIdeles.infiniteRealEmbedding K ((expUnit t : NNReal) : ℝ) =
        PositiveRealIdeles.infiniteRealEmbedding K (Real.exp (t - s)) * y := by
    rw [mul_right_comm, ← map_mul, Units.val_inv_eq_inv_val, NNReal.coe_inv, coe_expUnit,
      coe_expUnit, ← Real.exp_neg, ← Real.exp_add, neg_add_eq_sub]
  exact key _ _ _

end Langlands.Global
