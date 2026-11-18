import Langlands.Representation.Archimedean.RealPrincipalSeriesDualityProof
import Langlands.LinearAlgebra.TriangularUnitary
import Langlands.Representation.RankinSelberg.QuotientIntegrals
import Mathlib.Topology.Maps.Proper.Basic

/-! # The Iwasawa decomposition of `GL_n(ℝ)` with continuous coordinates -/

noncomputable section

open Matrix

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealIwasawa

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (upperUnipotent)

variable {n : ℕ}

/-! ### Upper triangular matrices with positive diagonal -/

/-- A real matrix is upper triangular with positive diagonal entries. -/
def IsPosUpper (b : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  b.IsUpperTriangular ∧ ∀ i, 0 < b i i

theorem upper_mul_diag {A C : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsUpperTriangular) (hC : C.IsUpperTriangular) (i : Fin n) :
    (A * C) i i = A i i * C i i := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single i]
  intro j hji
  rcases lt_or_gt_of_ne hji with hji | hij
  · rw [hA hji, zero_mul]
  · rw [hC hij, mul_zero]

theorem IsPosUpper.mul {b c : Matrix (Fin n) (Fin n) ℝ} (hb : IsPosUpper b)
    (hc : IsPosUpper c) : IsPosUpper (b * c) :=
  ⟨hb.1.mul hc.1, fun i => by
    rw [upper_mul_diag hb.1 hc.1]
    exact mul_pos (hb.2 i) (hc.2 i)⟩

/-- An upper triangular orthogonal matrix with positive diagonal is the identity. -/
theorem eq_one_of_isPosUpper {c : Matrix (Fin n) (Fin n) ℝ} (hc : IsPosUpper c)
    (hcc : cᵀ * c = 1) : c = 1 := by
  have hinv : c⁻¹ = cᵀ := Matrix.inv_eq_left_inv hcc
  let _ : Invertible c := invertibleOfLeftInverse c cᵀ hcc
  have hu : (cᵀ).IsUpperTriangular := hinv ▸ Matrix.blockTriangular_inv_of_blockTriangular hc.1
  have hoff : ∀ i j, i ≠ j → c i j = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · have h' := hu h
      simpa [Matrix.transpose_apply] using h'
    · exact hc.1 h
  have hdiag : ∀ i, c i i = 1 := by
    intro i
    have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i i) hcc
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h
    rw [Fintype.sum_eq_single i (fun j hj => by rw [hoff j i hj, mul_zero])] at h
    rcases mul_self_eq_one_iff.mp h with h1 | h1
    · exact h1
    · have := hc.2 i
      linarith
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [hdiag i, Matrix.one_apply_eq]
  · rw [hoff i j hij, Matrix.one_apply_ne hij]

/-- Every invertible real matrix is an upper triangular matrix with positive diagonal times an
orthogonal matrix. -/
theorem exists_isPosUpper_mul_orthogonal (g : Matrix (Fin n) (Fin n) ℝ) (hg : IsUnit g) :
    ∃ b k : Matrix (Fin n) (Fin n) ℝ, IsPosUpper b ∧ k ∈ Matrix.unitaryGroup (Fin n) ℝ ∧
      g = b * k := by
  obtain ⟨b, u, hb, hbu, hu, rfl⟩ :=
    LinearAlgebra.TriangularUnitary.exists_upperTriangular_mul_unitary g hg
  have hdet : b.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det b).mp hbu).ne_zero
  have hne : ∀ i, b i i ≠ 0 := by
    intro i hi
    apply hdet
    rw [Matrix.det_of_isUpperTriangular hb]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  set s : Fin n → ℝ := fun i => if 0 < b i i then 1 else -1 with hs
  have hss : ∀ i, s i * s i = 1 := by
    intro i
    simp only [hs]
    split_ifs <;> norm_num
  have hS : diagonal s * diagonal s = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact hss i
  refine ⟨b * diagonal s, diagonal s * u,
    ⟨LinearAlgebra.TriangularUnitary.isUpperTriangular_mul_diagonal hb s, fun i => ?_⟩, ?_, ?_⟩
  · rw [mul_diagonal]
    simp only [hs]
    split_ifs with h
    · simpa using h
    · have h' : b i i < 0 := lt_of_le_of_ne (not_lt.mp h) (hne i)
      linarith
  · refine (Matrix.unitaryGroup (Fin n) ℝ).mul_mem ?_ hu
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, diagonal_conjTranspose]
    have hst : star s = s := by
      funext i
      exact star_trivial _
    rw [hst, hS]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal s), hS, Matrix.one_mul]

/-! ### The orthogonal Iwasawa coordinate -/

/-- The value of the inverse of an orthogonal element is its transpose. -/
theorem val_inv_of_mem (k : unitaryCompact ℝ n) :
    (((k : Langlands.GeneralLinear n ℝ)⁻¹ : Langlands.GeneralLinear n ℝ) :
      Matrix (Fin n) (Fin n) ℝ) = ((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ := by
  rw [Matrix.GeneralLinearGroup.coe_inv]
  exact Matrix.inv_eq_left_inv (Archimedean.RealPrincipalSeriesDuality.transpose_mul_self_of_mem k)

/-- An invertible upper triangular matrix has nonzero diagonal entries. -/
theorem diag_ne_zero (g : Langlands.GeneralLinear n ℝ)
    (hg : (g : Matrix (Fin n) (Fin n) ℝ).IsUpperTriangular) (i : Fin n) :
    (g : Matrix (Fin n) (Fin n) ℝ) i i ≠ 0 := by
  intro hi
  have hdet : (g : Matrix (Fin n) (Fin n) ℝ).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  apply hdet
  rw [Matrix.det_of_isUpperTriangular hg]
  exact Finset.prod_eq_zero (Finset.mem_univ i) hi

theorem exists_kpart (g : Langlands.GeneralLinear n ℝ) :
    ∃ k : unitaryCompact ℝ n,
      IsPosUpper ((g * (k : Langlands.GeneralLinear n ℝ)⁻¹ : Langlands.GeneralLinear n ℝ) :
        Matrix (Fin n) (Fin n) ℝ) := by
  obtain ⟨b, k, hb, hk, hg⟩ := exists_isPosUpper_mul_orthogonal (g : Matrix (Fin n) (Fin n) ℝ)
    g.isUnit
  let kU : Langlands.GeneralLinear n ℝ := Unitary.toUnits ⟨k, hk⟩
  refine ⟨⟨kU, hk⟩, ?_⟩
  have hval : ((g * (kU)⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) = b := by
    rw [Units.val_mul, val_inv_of_mem ⟨kU, hk⟩]
    change (g : Matrix (Fin n) (Fin n) ℝ) * kᵀ = b
    have hkk : k * kᵀ = 1 := by
      have h := (Matrix.mem_unitaryGroup_iff).mp hk
      rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
    rw [hg, Matrix.mul_assoc, hkk, Matrix.mul_one]
  change IsPosUpper ((g * (kU)⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)
  rw [hval]
  exact hb

/-- The orthogonal Iwasawa coordinate: `g * (kpart g)⁻¹` is upper triangular with positive
diagonal. -/
def kpart (g : Langlands.GeneralLinear n ℝ) : unitaryCompact ℝ n :=
  (exists_kpart g).choose

theorem isPosUpper_mul_kpart_inv (g : Langlands.GeneralLinear n ℝ) :
    IsPosUpper ((g * (kpart g : Langlands.GeneralLinear n ℝ)⁻¹ : Langlands.GeneralLinear n ℝ) :
      Matrix (Fin n) (Fin n) ℝ) :=
  (exists_kpart g).choose_spec

theorem isPosUpper_inv {g : Langlands.GeneralLinear n ℝ}
    (hg : IsPosUpper (g : Matrix (Fin n) (Fin n) ℝ)) :
    IsPosUpper ((g⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) := by
  have hi : ((g⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ).IsUpperTriangular := by
    let _ := g.invertible
    simpa only [Matrix.GeneralLinearGroup.coe_inv] using
      Matrix.blockTriangular_inv_of_blockTriangular hg.1
  refine ⟨hi, fun i => ?_⟩
  have h : ((g : Matrix (Fin n) (Fin n) ℝ) *
      ((g⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)) i i =
      (1 : Matrix (Fin n) (Fin n) ℝ) i i := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [upper_mul_diag hg.1 hi, Matrix.one_apply_eq] at h
  exact (pos_iff_pos_of_mul_pos (h ▸ one_pos)).mp (hg.2 i)

/-- Uniqueness of the orthogonal Iwasawa coordinate. -/
theorem eq_of_isPosUpper {g : Langlands.GeneralLinear n ℝ} {k₁ k₂ : unitaryCompact ℝ n}
    (h₁ : IsPosUpper ((g * (k₁ : Langlands.GeneralLinear n ℝ)⁻¹ : Langlands.GeneralLinear n ℝ) :
      Matrix (Fin n) (Fin n) ℝ))
    (h₂ : IsPosUpper ((g * (k₂ : Langlands.GeneralLinear n ℝ)⁻¹ : Langlands.GeneralLinear n ℝ) :
      Matrix (Fin n) (Fin n) ℝ)) : k₁ = k₂ := by
  set c : Langlands.GeneralLinear n ℝ :=
    (g * (k₂ : Langlands.GeneralLinear n ℝ)⁻¹)⁻¹ * (g * (k₁ : Langlands.GeneralLinear n ℝ)⁻¹)
    with hcdef
  have hc : c = (k₂ : Langlands.GeneralLinear n ℝ) * (k₁ : Langlands.GeneralLinear n ℝ)⁻¹ := by
    rw [hcdef]
    group
  have hpos : IsPosUpper (c : Matrix (Fin n) (Fin n) ℝ) := by
    rw [hcdef, Units.val_mul]
    exact (isPosUpper_inv h₂).mul h₁
  have hmem : (k₂ : Langlands.GeneralLinear n ℝ) * (k₁ : Langlands.GeneralLinear n ℝ)⁻¹ ∈
      unitaryCompact ℝ n := mul_mem k₂.2 (inv_mem k₁.2)
  have hT : (c : Matrix (Fin n) (Fin n) ℝ)ᵀ * c = 1 := by
    rw [hc]
    exact Archimedean.RealPrincipalSeriesDuality.transpose_mul_self_of_mem ⟨_, hmem⟩
  have h1 : c = 1 := Units.ext (eq_one_of_isPosUpper hpos hT)
  rw [hc, mul_inv_eq_one] at h1
  exact Subtype.ext h1.symm

theorem kpart_eq {g : Langlands.GeneralLinear n ℝ} {k : unitaryCompact ℝ n}
    (h : IsPosUpper ((g * (k : Langlands.GeneralLinear n ℝ)⁻¹ : Langlands.GeneralLinear n ℝ) :
      Matrix (Fin n) (Fin n) ℝ)) : kpart g = k :=
  eq_of_isPosUpper (isPosUpper_mul_kpart_inv g) h

/-- The orthogonal Iwasawa coordinate is continuous (closed graph into a compact group). -/
theorem continuous_kpart : Continuous (kpart (n := n)) := by
  apply continuous_of_isClosed_graph
  have hset : Function.graph (kpart (n := n)) =
      {p : Langlands.GeneralLinear n ℝ × unitaryCompact ℝ n |
        ((p.1 * (p.2 : Langlands.GeneralLinear n ℝ)⁻¹ : Langlands.GeneralLinear n ℝ) :
          Matrix (Fin n) (Fin n) ℝ).IsUpperTriangular} ∩
      ⋂ i : Fin n, {p : Langlands.GeneralLinear n ℝ × unitaryCompact ℝ n |
        0 ≤ ((p.1 * (p.2 : Langlands.GeneralLinear n ℝ)⁻¹ : Langlands.GeneralLinear n ℝ) :
          Matrix (Fin n) (Fin n) ℝ) i i} := by
    ext ⟨g, k⟩
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    change kpart g = k ↔ _
    constructor
    · rintro rfl
      exact ⟨(isPosUpper_mul_kpart_inv g).1, fun i => ((isPosUpper_mul_kpart_inv g).2 i).le⟩
    · rintro ⟨hu, hnn⟩
      exact kpart_eq ⟨hu, fun i => lt_of_le_of_ne (hnn i) (diag_ne_zero _ hu i).symm⟩
  rw [hset]
  have hcont : Continuous fun p : Langlands.GeneralLinear n ℝ × unitaryCompact ℝ n =>
      ((p.1 * (p.2 : Langlands.GeneralLinear n ℝ)⁻¹ : Langlands.GeneralLinear n ℝ) :
        Matrix (Fin n) (Fin n) ℝ) :=
    Units.continuous_val.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd).inv)
  exact IsClosed.inter (isClosed_setOfPred_blockTriangular.preimage hcont)
    (isClosed_iInter fun i => isClosed_le continuous_const ((continuous_apply_apply i i).comp hcont))

/-! ### The positive diagonal torus -/

/-- The positive diagonal matrix `diag(exp y_i)` as an element of `GL_n(ℝ)`. -/
def torus (y : Fin n → ℝ) : Langlands.GeneralLinear n ℝ where
  val := diagonal fun i => Real.exp (y i)
  inv := diagonal fun i => Real.exp (-y i)
  val_inv := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  inv_val := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

@[simp] theorem torus_val (y : Fin n → ℝ) :
    ((torus y : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) =
      diagonal fun i => Real.exp (y i) := rfl

theorem torus_add (y z : Fin n → ℝ) : torus (y + z) = torus y * torus z := by
  apply Units.ext
  rw [Units.val_mul, torus_val, torus_val, torus_val, diagonal_mul_diagonal]
  congr 1
  funext i
  rw [Pi.add_apply, Real.exp_add]

theorem torus_zero : torus (0 : Fin n → ℝ) = 1 := by
  apply Units.ext
  rw [torus_val, Units.val_one, ← diagonal_one]
  congr 1
  funext i
  rw [Pi.zero_apply, Real.exp_zero]

theorem torus_neg (y : Fin n → ℝ) : torus (-y) = (torus y)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← torus_add, neg_add_cancel, torus_zero]

theorem continuous_torus : Continuous (torus (n := n)) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun y : Fin n → ℝ => diagonal fun i => Real.exp (y i)
    exact Continuous.matrix_diagonal
      (continuous_pi fun i => Real.continuous_exp.comp (continuous_apply i))
  · change Continuous fun y : Fin n → ℝ => diagonal fun i => Real.exp (-y i)
    exact Continuous.matrix_diagonal
      (continuous_pi fun i => Real.continuous_exp.comp (continuous_apply i).neg)

theorem isPosUpper_torus (y : Fin n → ℝ) :
    IsPosUpper ((torus y : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) := by
  refine ⟨?_, fun i => ?_⟩
  · rw [torus_val]
    exact Matrix.blockTriangular_diagonal _
  · rw [torus_val, diagonal_apply_eq]
    exact Real.exp_pos _

theorem isPosUpper_of_mem_upperUnipotent {u : Langlands.GeneralLinear n ℝ}
    (hu : u ∈ upperUnipotent n ℝ) :
    IsPosUpper (u : Matrix (Fin n) (Fin n) ℝ) :=
  ⟨hu.1, fun i => by
    have h : u i i = 1 := hu.2 i
    change 0 < u i i
    rw [h]
    exact one_pos⟩

/-! ### The triangular and logarithmic toral Iwasawa coordinates -/

/-- The triangular Iwasawa coordinate `g * (kpart g)⁻¹`. -/
def bpart (g : Langlands.GeneralLinear n ℝ) : Langlands.GeneralLinear n ℝ :=
  g * (kpart g : Langlands.GeneralLinear n ℝ)⁻¹

theorem isPosUpper_bpart (g : Langlands.GeneralLinear n ℝ) :
    IsPosUpper ((bpart g : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) :=
  isPosUpper_mul_kpart_inv g

theorem bpart_mul_kpart (g : Langlands.GeneralLinear n ℝ) :
    bpart g * (kpart g : Langlands.GeneralLinear n ℝ) = g := by
  rw [bpart, inv_mul_cancel_right]

/-- The logarithmic toral Iwasawa coordinate: the logarithms of the diagonal entries of
`bpart g`. -/
def alpha (g : Langlands.GeneralLinear n ℝ) : Fin n → ℝ :=
  fun i => Real.log ((bpart g : Langlands.GeneralLinear n ℝ) i i)

theorem exp_alpha (g : Langlands.GeneralLinear n ℝ) (i : Fin n) :
    Real.exp (alpha g i) = (bpart g : Langlands.GeneralLinear n ℝ) i i :=
  Real.exp_log ((isPosUpper_bpart g).2 i)

theorem npart_mem (g : Langlands.GeneralLinear n ℝ) :
    bpart g * torus (-alpha g) ∈ upperUnipotent n ℝ := by
  refine ⟨?_, fun i => ?_⟩
  · rw [Units.val_mul, torus_val]
    exact LinearAlgebra.TriangularUnitary.isUpperTriangular_mul_diagonal
      (isPosUpper_bpart g).1 _
  · change ((bpart g : Matrix (Fin n) (Fin n) ℝ) *
      ((torus (-alpha g) : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)) i i = 1
    rw [torus_val, mul_diagonal, Pi.neg_apply, Real.exp_neg, exp_alpha]
    exact mul_inv_cancel₀ ((isPosUpper_bpart g).2 i).ne'

/-- The unipotent Iwasawa coordinate. -/
def npart (g : Langlands.GeneralLinear n ℝ) : upperUnipotent n ℝ :=
  ⟨bpart g * torus (-alpha g), npart_mem g⟩

/-- The Iwasawa decomposition `g = npart g * torus (alpha g) * kpart g`. -/
theorem npart_mul_torus_mul_kpart (g : Langlands.GeneralLinear n ℝ) :
    (npart g : Langlands.GeneralLinear n ℝ) * torus (alpha g) *
      (kpart g : Langlands.GeneralLinear n ℝ) = g := by
  change bpart g * torus (-alpha g) * torus (alpha g) * (kpart g : Langlands.GeneralLinear n ℝ) = g
  rw [torus_neg, inv_mul_cancel_right, bpart_mul_kpart]

theorem isPosUpper_unipotent_mul_torus (u : upperUnipotent n ℝ) (y : Fin n → ℝ) :
    IsPosUpper (((u : Langlands.GeneralLinear n ℝ) * torus y : Langlands.GeneralLinear n ℝ) :
      Matrix (Fin n) (Fin n) ℝ) := by
  rw [Units.val_mul]
  exact (isPosUpper_of_mem_upperUnipotent u.2).mul (isPosUpper_torus y)

theorem kpart_iwasawa (u : upperUnipotent n ℝ) (y : Fin n → ℝ) (k : unitaryCompact ℝ n) :
    kpart ((u : Langlands.GeneralLinear n ℝ) * torus y * (k : Langlands.GeneralLinear n ℝ)) = k := by
  apply kpart_eq
  rw [mul_inv_cancel_right]
  exact isPosUpper_unipotent_mul_torus u y

theorem bpart_iwasawa (u : upperUnipotent n ℝ) (y : Fin n → ℝ) (k : unitaryCompact ℝ n) :
    bpart ((u : Langlands.GeneralLinear n ℝ) * torus y * (k : Langlands.GeneralLinear n ℝ)) =
      (u : Langlands.GeneralLinear n ℝ) * torus y := by
  rw [bpart, kpart_iwasawa, mul_inv_cancel_right]

theorem alpha_iwasawa (u : upperUnipotent n ℝ) (y : Fin n → ℝ) (k : unitaryCompact ℝ n) :
    alpha ((u : Langlands.GeneralLinear n ℝ) * torus y * (k : Langlands.GeneralLinear n ℝ)) = y := by
  funext i
  have h := upper_mul_diag (isPosUpper_of_mem_upperUnipotent u.2).1 (isPosUpper_torus y).1 i
  have hu : ((u : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) i i = 1 := u.2.2 i
  rw [hu, one_mul, torus_val, diagonal_apply_eq] at h
  change Real.log ((bpart ((u : Langlands.GeneralLinear n ℝ) * torus y *
    (k : Langlands.GeneralLinear n ℝ)) : Matrix (Fin n) (Fin n) ℝ) i i) = y i
  rw [bpart_iwasawa, Units.val_mul, torus_val, h, Real.log_exp]

theorem npart_iwasawa (u : upperUnipotent n ℝ) (y : Fin n → ℝ) (k : unitaryCompact ℝ n) :
    npart ((u : Langlands.GeneralLinear n ℝ) * torus y * (k : Langlands.GeneralLinear n ℝ)) = u := by
  apply Subtype.ext
  change bpart ((u : Langlands.GeneralLinear n ℝ) * torus y * (k : Langlands.GeneralLinear n ℝ)) *
    torus (-alpha ((u : Langlands.GeneralLinear n ℝ) * torus y *
      (k : Langlands.GeneralLinear n ℝ))) = u
  rw [bpart_iwasawa, alpha_iwasawa, torus_neg, mul_inv_cancel_right]

/-! ### Equivariance -/

theorem alpha_mul_unitary (g : Langlands.GeneralLinear n ℝ) (k : unitaryCompact ℝ n) :
    alpha (g * (k : Langlands.GeneralLinear n ℝ)) = alpha g := by
  conv_lhs => rw [← npart_mul_torus_mul_kpart g]
  rw [mul_assoc _ (kpart g : Langlands.GeneralLinear n ℝ)]
  exact alpha_iwasawa (npart g) (alpha g) (kpart g * k)

theorem npart_mul_unitary (g : Langlands.GeneralLinear n ℝ) (k : unitaryCompact ℝ n) :
    npart (g * (k : Langlands.GeneralLinear n ℝ)) = npart g := by
  conv_lhs => rw [← npart_mul_torus_mul_kpart g]
  rw [mul_assoc _ (kpart g : Langlands.GeneralLinear n ℝ)]
  exact npart_iwasawa (npart g) (alpha g) (kpart g * k)

theorem alpha_unipotent_mul (h : upperUnipotent n ℝ) (g : Langlands.GeneralLinear n ℝ) :
    alpha ((h : Langlands.GeneralLinear n ℝ) * g) = alpha g := by
  conv_lhs => rw [← npart_mul_torus_mul_kpart g]
  rw [← mul_assoc, ← mul_assoc]
  exact alpha_iwasawa (h * npart g) (alpha g) (kpart g)

theorem npart_unipotent_mul (h : upperUnipotent n ℝ) (g : Langlands.GeneralLinear n ℝ) :
    npart ((h : Langlands.GeneralLinear n ℝ) * g) = h * npart g := by
  conv_lhs => rw [← npart_mul_torus_mul_kpart g]
  rw [← mul_assoc, ← mul_assoc]
  exact npart_iwasawa (h * npart g) (alpha g) (kpart g)

theorem conjTorus_mem (z : Fin n → ℝ) (u : upperUnipotent n ℝ) :
    torus z * (u : Langlands.GeneralLinear n ℝ) * torus (-z) ∈ upperUnipotent n ℝ := by
  have hu := isPosUpper_of_mem_upperUnipotent u.2
  have h1 := (isPosUpper_torus z).1.mul hu.1
  refine ⟨?_, fun i => ?_⟩
  · rw [Units.val_mul, Units.val_mul]
    exact h1.mul (isPosUpper_torus (-z)).1
  · change ((((torus z : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) *
      ((u : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)) *
      ((torus (-z) : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)) i i = 1
    have hui : ((u : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) i i = 1 := u.2.2 i
    rw [upper_mul_diag h1 (isPosUpper_torus (-z)).1, upper_mul_diag (isPosUpper_torus z).1 hu.1,
      hui, torus_val, torus_val, diagonal_apply_eq, diagonal_apply_eq, mul_one, Pi.neg_apply,
      ← Real.exp_add, add_neg_cancel, Real.exp_zero]

/-- Conjugation of a unipotent element by a positive diagonal torus element. -/
def conjTorus (z : Fin n → ℝ) (u : upperUnipotent n ℝ) : upperUnipotent n ℝ :=
  ⟨torus z * (u : Langlands.GeneralLinear n ℝ) * torus (-z), conjTorus_mem z u⟩

theorem torus_mul_eq (z : Fin n → ℝ) (g : Langlands.GeneralLinear n ℝ) :
    torus z * g = (conjTorus z (npart g) : Langlands.GeneralLinear n ℝ) * torus (z + alpha g) *
      (kpart g : Langlands.GeneralLinear n ℝ) := by
  conv_lhs => rw [← npart_mul_torus_mul_kpart g]
  change _ = torus z * (npart g : Langlands.GeneralLinear n ℝ) * torus (-z) *
    torus (z + alpha g) * (kpart g : Langlands.GeneralLinear n ℝ)
  rw [torus_add, torus_neg]
  group

theorem alpha_torus_mul (z : Fin n → ℝ) (g : Langlands.GeneralLinear n ℝ) :
    alpha (torus z * g) = z + alpha g := by
  rw [torus_mul_eq]
  exact alpha_iwasawa _ _ _

theorem npart_torus_mul (z : Fin n → ℝ) (g : Langlands.GeneralLinear n ℝ) :
    npart (torus z * g) = conjTorus z (npart g) := by
  rw [torus_mul_eq]
  exact npart_iwasawa _ _ _

/-! ### Continuity -/

theorem continuous_bpart : Continuous (bpart (n := n)) :=
  continuous_id.mul (continuous_subtype_val.comp continuous_kpart).inv

theorem continuous_alpha : Continuous (alpha (n := n)) := by
  have hb : Continuous fun g : Langlands.GeneralLinear n ℝ =>
      ((bpart g : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) :=
    Units.continuous_val.comp continuous_bpart
  refine continuous_pi fun i => ?_
  exact Continuous.log ((continuous_apply_apply i i).comp hb)
    fun g => ((isPosUpper_bpart g).2 i).ne'

theorem continuous_npart : Continuous (npart (n := n)) :=
  Continuous.subtype_mk (continuous_bpart.mul (continuous_torus.comp continuous_alpha.neg)) _

theorem continuous_conjTorus (u : upperUnipotent n ℝ) :
    Continuous fun z : Fin n → ℝ => conjTorus z u :=
  Continuous.subtype_mk ((continuous_torus.mul continuous_const).mul
    (continuous_torus.comp continuous_neg)) _

/-! ### Descent to the unipotent quotient -/

open Langlands.QuotientIntegration (LeftQuotient descend)

/-- The logarithmic toral Iwasawa coordinate on the coset space `N \ GL_n(ℝ)`. -/
def alphaQ : LeftQuotient (upperUnipotent n ℝ) → (Fin n → ℝ) :=
  descend (upperUnipotent n ℝ) alpha alpha_unipotent_mul

@[simp] theorem alphaQ_mk (g : Langlands.GeneralLinear n ℝ) :
    alphaQ (Quotient.mk (QuotientGroup.rightRel (upperUnipotent n ℝ)) g) = alpha g := rfl

theorem continuous_alphaQ : Continuous (alphaQ (n := n)) := by
  unfold alphaQ descend
  exact continuous_alpha.quotient_lift _

theorem alpha_torus_mul_unitary (y : Fin n → ℝ) (k : unitaryCompact ℝ n) :
    alpha (torus y * (k : Langlands.GeneralLinear n ℝ)) = y := by
  have h := alpha_iwasawa 1 y k
  rwa [OneMemClass.coe_one, one_mul] at h

theorem mk_eq_mk_torus_mul_kpart (g : Langlands.GeneralLinear n ℝ) :
    Quotient.mk (QuotientGroup.rightRel (upperUnipotent n ℝ)) g =
      Quotient.mk _ (torus (alpha g) * (kpart g : Langlands.GeneralLinear n ℝ)) := by
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  have h : torus (alpha g) * (kpart g : Langlands.GeneralLinear n ℝ) =
      ((npart g : Langlands.GeneralLinear n ℝ))⁻¹ * g := by
    rw [eq_inv_mul_iff_mul_eq, ← mul_assoc]
    exact npart_mul_torus_mul_kpart g
  rw [h, mul_inv_cancel_right]
  exact inv_mem (npart g).2

/-- The preimage of a set of logarithmic toral coordinates is the image of the set times the
orthogonal group. -/
theorem alphaQ_preimage (C : Set (Fin n → ℝ)) :
    alphaQ ⁻¹' C = (fun p : (Fin n → ℝ) × unitaryCompact ℝ n =>
      Quotient.mk (QuotientGroup.rightRel (upperUnipotent n ℝ))
        (torus p.1 * (p.2 : Langlands.GeneralLinear n ℝ))) '' (C ×ˢ Set.univ) := by
  ext q
  induction q using Quotient.inductionOn with
  | h g =>
    constructor
    · intro hg
      exact ⟨(alpha g, kpart g), ⟨hg, Set.mem_univ _⟩, (mk_eq_mk_torus_mul_kpart g).symm⟩
    · rintro ⟨⟨y, k⟩, ⟨hy, -⟩, hq⟩
      change alphaQ (Quotient.mk _ g) ∈ C
      rw [← hq, alphaQ_mk, alpha_torus_mul_unitary]
      exact hy

theorem continuous_mk_torus_mul :
    Continuous (fun p : (Fin n → ℝ) × unitaryCompact ℝ n =>
      Quotient.mk (QuotientGroup.rightRel (upperUnipotent n ℝ))
        (torus p.1 * (p.2 : Langlands.GeneralLinear n ℝ))) :=
  continuous_quotient_mk'.comp
    ((continuous_torus.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd))

/-- Preimages of compact sets under the logarithmic toral coordinate are compact. -/
theorem isCompact_alphaQ_preimage {C : Set (Fin n → ℝ)} (hC : IsCompact C) :
    IsCompact (alphaQ ⁻¹' C) := by
  rw [alphaQ_preimage]
  exact (hC.prod isCompact_univ).image continuous_mk_torus_mul

end Langlands.Global.RankinSelbergGlobal.RealIwasawa
