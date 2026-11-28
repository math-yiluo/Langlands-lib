import Langlands.Representation.Shahidi.OpenCellLift

/-! # A matrix identity for the open cell of the `(1, n)` parabolic

For `GL_(1+(t+2))` with indices split as the first index, the middle indices `1, …, t+1` and
the last index, and a column `y = (y', c)` with `c ≠ 0`,

`lower(y) = p₀ · lower((y'/c, 0)) · κ`,

where `p₀` is the upper block-triangular matrix with diagonal blocks `c⁻¹` and
`[[I, y'], [0, c]]` and entry `1` in the corner `(first, last)`, and the right factor `κ` is the
matrix that differs from the identity only in the rows and columns `first`, `last`, where it is
`[[0, -1], [1, c⁻¹]]` (so `κ` is integral exactly when `c⁻¹` is, over a valued field). Also, for
every `c`, `lower(y) = diag(lower(y'), 1) · ℓ(c)` with `ℓ(c)` the elementary lower matrix with
entry `c` at `(last, first)`. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell.Base

open Langlands.GeneralLinear Matrix

variable {F : Type*} (t : ℕ)

/-- The first index of `Fin ((0+1)+((t+1)+1))`. -/
def aI : Fin ((0 + 1) + ((t + 1) + 1)) := Fin.castAdd ((t + 1) + 1) 0

/-- The index of the `j`-th entry of the second block. -/
def cI (j : Fin ((t + 1) + 1)) : Fin ((0 + 1) + ((t + 1) + 1)) := Fin.natAdd (0 + 1) j

/-- A middle index. -/
def mI (j : Fin (t + 1)) : Fin ((0 + 1) + ((t + 1) + 1)) := cI t j.castSucc

/-- The last index. -/
def lI : Fin ((0 + 1) + ((t + 1) + 1)) := cI t (Fin.last (t + 1))

theorem index_cases (i : Fin ((0 + 1) + ((t + 1) + 1))) :
    i = aI t ∨ (∃ j, i = mI t j) ∨ i = lI t := by
  unfold aI mI lI cI
  refine Fin.addCases (fun i₀ => ?_) (fun j => ?_) i
  · left
    have : i₀ = 0 := Fin.ext (by have := i₀.isLt; omega)
    rw [this]
  · right
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · right
      rfl
    · left
      exact ⟨j', rfl⟩

theorem sum_index {M : Type*} [AddCommMonoid M] (f : Fin ((0 + 1) + ((t + 1) + 1)) → M) :
    ∑ i, f i = f (aI t) + ∑ j : Fin (t + 1), f (mI t j) + f (lI t) := by
  unfold aI mI lI cI
  rw [Fin.sum_univ_add, Fin.sum_univ_castSucc (f := fun j => f (Fin.natAdd (0 + 1) j)),
    Fin.sum_univ_succ (f := fun i : Fin (0 + 1) => f (Fin.castAdd ((t + 1) + 1) i)),
    Fin.sum_univ_zero, add_zero, ← add_assoc]

theorem mI_injective : Function.Injective (mI t) := by
  intro j k h
  unfold mI cI at h
  exact Fin.castSucc_injective _ ((Fin.natAdd_inj _).1 h)

@[simp] theorem aI_ne_mI (j : Fin (t + 1)) : aI t ≠ mI t j := by
  intro h
  have := congrArg Fin.val h
  simp only [aI, mI, cI, Fin.val_castAdd, Fin.val_natAdd, Fin.val_castSucc, Fin.val_zero] at this
  omega

@[simp] theorem mI_ne_aI (j : Fin (t + 1)) : mI t j ≠ aI t := fun h => aI_ne_mI t j h.symm

@[simp] theorem aI_ne_lI : aI t ≠ lI t := by
  intro h
  have := congrArg Fin.val h
  simp only [aI, lI, cI, Fin.val_castAdd, Fin.val_natAdd, Fin.val_last, Fin.val_zero] at this
  omega

@[simp] theorem lI_ne_aI : lI t ≠ aI t := fun h => aI_ne_lI t h.symm

@[simp] theorem mI_ne_lI (j : Fin (t + 1)) : mI t j ≠ lI t := by
  intro h
  have := congrArg Fin.val h
  simp only [mI, lI, cI, Fin.val_natAdd, Fin.val_castSucc, Fin.val_last] at this
  omega

@[simp] theorem lI_ne_mI (j : Fin (t + 1)) : lI t ≠ mI t j := fun h => mI_ne_lI t j h.symm

@[simp] theorem mI_inj (j k : Fin (t + 1)) : mI t j = mI t k ↔ j = k :=
  (mI_injective t).eq_iff

/-- A `3 × 3` block matrix for the blocks `1`, `t + 1`, `1`. -/
def blk (aa : F) (am : Fin (t + 1) → F) (al : F) (ma : Fin (t + 1) → F)
    (mm : Fin (t + 1) → Fin (t + 1) → F) (ml : Fin (t + 1) → F) (la : F)
    (lm : Fin (t + 1) → F) (ll : F) : Matrix (Fin ((0 + 1) + ((t + 1) + 1)))
      (Fin ((0 + 1) + ((t + 1) + 1))) F :=
  Matrix.of fun i k =>
    Fin.addCases
      (fun _ => Fin.addCases (fun _ => aa)
        (fun k' => Fin.lastCases al (fun k'' => am k'') k') k)
      (fun i' => Fin.lastCases
        (Fin.addCases (fun _ => la) (fun k' => Fin.lastCases ll (fun k'' => lm k'') k') k)
        (fun i'' => Fin.addCases (fun _ => ma i'')
          (fun k' => Fin.lastCases (ml i'') (fun k'' => mm i'' k'') k') k) i') i

variable {t}
variable (aa : F) (am : Fin (t + 1) → F) (al : F) (ma : Fin (t + 1) → F)
    (mm : Fin (t + 1) → Fin (t + 1) → F) (ml : Fin (t + 1) → F) (la : F)
    (lm : Fin (t + 1) → F) (ll : F)

@[simp] theorem blk_aa :
    blk t aa am al ma mm ml la lm ll (aI t) (aI t) = aa := by
  simp only [blk, aI, of_apply, Fin.addCases_left]

@[simp] theorem blk_am (j : Fin (t + 1)) :
    blk t aa am al ma mm ml la lm ll (aI t) (mI t j) = am j := by
  simp only [blk, aI, mI, cI, of_apply, Fin.addCases_left, Fin.addCases_right, Fin.lastCases_castSucc]

@[simp] theorem blk_al :
    blk t aa am al ma mm ml la lm ll (aI t) (lI t) = al := by
  simp only [blk, aI, lI, cI, of_apply, Fin.addCases_left, Fin.addCases_right, Fin.lastCases_last]

@[simp] theorem blk_ma (j : Fin (t + 1)) :
    blk t aa am al ma mm ml la lm ll (mI t j) (aI t) = ma j := by
  simp only [blk, aI, mI, cI, of_apply, Fin.addCases_left, Fin.addCases_right, Fin.lastCases_castSucc]

@[simp] theorem blk_mm (j k : Fin (t + 1)) :
    blk t aa am al ma mm ml la lm ll (mI t j) (mI t k) = mm j k := by
  simp only [blk, mI, cI, of_apply, Fin.addCases_right, Fin.lastCases_castSucc]

@[simp] theorem blk_ml (j : Fin (t + 1)) :
    blk t aa am al ma mm ml la lm ll (mI t j) (lI t) = ml j := by
  simp only [blk, mI, lI, cI, of_apply, Fin.addCases_right, Fin.lastCases_castSucc, Fin.lastCases_last]

@[simp] theorem blk_la :
    blk t aa am al ma mm ml la lm ll (lI t) (aI t) = la := by
  simp only [blk, aI, lI, cI, of_apply, Fin.addCases_left, Fin.addCases_right, Fin.lastCases_last]

@[simp] theorem blk_lm (j : Fin (t + 1)) :
    blk t aa am al ma mm ml la lm ll (lI t) (mI t j) = lm j := by
  simp only [blk, mI, lI, cI, of_apply, Fin.addCases_right, Fin.lastCases_last, Fin.lastCases_castSucc]

@[simp] theorem blk_ll :
    blk t aa am al ma mm ml la lm ll (lI t) (lI t) = ll := by
  simp only [blk, lI, cI, of_apply, Fin.addCases_right, Fin.lastCases_last]

theorem blk_ext {M N : Matrix (Fin ((0 + 1) + ((t + 1) + 1))) (Fin ((0 + 1) + ((t + 1) + 1))) F}
    (h1 : M (aI t) (aI t) = N (aI t) (aI t)) (h2 : ∀ j, M (aI t) (mI t j) = N (aI t) (mI t j))
    (h3 : M (aI t) (lI t) = N (aI t) (lI t)) (h4 : ∀ j, M (mI t j) (aI t) = N (mI t j) (aI t))
    (h5 : ∀ j k, M (mI t j) (mI t k) = N (mI t j) (mI t k))
    (h6 : ∀ j, M (mI t j) (lI t) = N (mI t j) (lI t)) (h7 : M (lI t) (aI t) = N (lI t) (aI t))
    (h8 : ∀ j, M (lI t) (mI t j) = N (lI t) (mI t j)) (h9 : M (lI t) (lI t) = N (lI t) (lI t)) :
    M = N := by
  ext i k
  rcases index_cases t i with rfl | ⟨j, rfl⟩ | rfl <;>
    rcases index_cases t k with rfl | ⟨k, rfl⟩ | rfl <;> simp_all

theorem mul_apply_index [NonUnitalNonAssocSemiring F]
    (M N : Matrix (Fin ((0 + 1) + ((t + 1) + 1))) (Fin ((0 + 1) + ((t + 1) + 1))) F)
    (i k : Fin ((0 + 1) + ((t + 1) + 1))) :
    (M * N) i k = M i (aI t) * N (aI t) k + ∑ j : Fin (t + 1), M i (mI t j) * N (mI t j) k +
      M i (lI t) * N (lI t) k := by
  rw [Matrix.mul_apply, sum_index]

section Identity

variable [Field F]

/-- The parabolic factor `p₀`. -/
def p0Mat (y : Matrix (Fin ((t + 1) + 1)) (Fin 1) F) :
    Matrix (Fin ((0 + 1) + ((t + 1) + 1))) (Fin ((0 + 1) + ((t + 1) + 1))) F :=
  blk t (y (Fin.last (t + 1)) 0)⁻¹ 0 1 0 (fun j k => if j = k then 1 else 0) (fun j => y j.castSucc 0) 0 0
    (y (Fin.last (t + 1)) 0)

/-- The matrix that is a two-sided inverse of `p₀` when the last entry `c` of `y` is nonzero
(`p0Mat_mul_inv`, `p0Mat_inv_mul`). -/
def p0InvMat (y : Matrix (Fin ((t + 1) + 1)) (Fin 1) F) :
    Matrix (Fin ((0 + 1) + ((t + 1) + 1))) (Fin ((0 + 1) + ((t + 1) + 1))) F :=
  blk t (y (Fin.last (t + 1)) 0) 0 (-1) 0 (fun j k => if j = k then 1 else 0)
    (fun j => -(y j.castSucc 0 * (y (Fin.last (t + 1)) 0)⁻¹)) 0 0 (y (Fin.last (t + 1)) 0)⁻¹

/-- The right factor `κ` (integral over `𝒪` when `c⁻¹ ∈ 𝒪`). -/
def kkMat (c : F) :
    Matrix (Fin ((0 + 1) + ((t + 1) + 1))) (Fin ((0 + 1) + ((t + 1) + 1))) F :=
  blk t 0 0 (-1) 0 (fun j k => if j = k then 1 else 0) 0 1 0 c⁻¹

/-- The inverse of `κ`. -/
def kkInvMat (c : F) :
    Matrix (Fin ((0 + 1) + ((t + 1) + 1))) (Fin ((0 + 1) + ((t + 1) + 1))) F :=
  blk t c⁻¹ 0 1 0 (fun j k => if j = k then 1 else 0) 0 (-1) 0 0

/-- The lower unipotent matrix of a column, in block form. -/
def lowerMat (y : Matrix (Fin ((t + 1) + 1)) (Fin 1) F) :
    Matrix (Fin ((0 + 1) + ((t + 1) + 1))) (Fin ((0 + 1) + ((t + 1) + 1))) F :=
  blk t 1 0 0 (fun j => y j.castSucc 0) (fun j k => if j = k then 1 else 0) 0
    (y (Fin.last (t + 1)) 0) 0 1

/-- The lower unipotent matrix of `(z, 0)`. -/
def lowerZeroMat (z : Matrix (Fin (t + 1)) (Fin 1) F) :
    Matrix (Fin ((0 + 1) + ((t + 1) + 1))) (Fin ((0 + 1) + ((t + 1) + 1))) F :=
  blk t 1 0 0 (fun j => z j 0) (fun j k => if j = k then 1 else 0) 0 0 0 1

theorem lower_val_eq (y : Matrix (Fin ((t + 1) + 1)) (Fin 1) F) :
    (lower (0 + 1) ((t + 1) + 1) F y : Matrix _ _ F) = lowerMat y := by
  have hl : ∀ j : Fin (t + 1), Fin.last (t + 1) ≠ j.castSucc := fun j h =>
    Fin.castSucc_ne_last j h.symm
  apply blk_ext <;> intros <;>
    simp only [lowerMat, blk_aa, blk_am, blk_al, blk_ma, blk_mm, blk_ml, blk_la, blk_lm, blk_ll] <;>
    simp only [aI, mI, lI, cI, lower_first_first, lower_first_second, lower_second_first,
      lower_second_second] <;> simp [Fin.castSucc_inj, hl]

/-- **The matrix identity** `lower(y) = p₀ · lower((y'/c, 0)) · κ`. -/
theorem lowerMat_eq (y : Matrix (Fin ((t + 1) + 1)) (Fin 1) F)
    (hc : y (Fin.last (t + 1)) 0 ≠ 0) :
    lowerMat y = p0Mat y * lowerZeroMat (Matrix.of fun j (_ : Fin 1) =>
      y j.castSucc 0 * (y (Fin.last (t + 1)) 0)⁻¹) * kkMat (y (Fin.last (t + 1)) 0) := by
  apply blk_ext <;> intros <;>
    simp [mul_apply_index, p0Mat, lowerZeroMat, kkMat, lowerMat, Finset.sum_ite_eq,
      Finset.sum_ite_eq', hc]

theorem p0Mat_mul_inv (y : Matrix (Fin ((t + 1) + 1)) (Fin 1) F)
    (hc : y (Fin.last (t + 1)) 0 ≠ 0) : p0Mat y * p0InvMat y = 1 := by
  apply blk_ext <;> intros <;>
    simp [mul_apply_index, p0Mat, p0InvMat, Matrix.one_apply, Finset.sum_ite_eq,
      Finset.sum_ite_eq', hc]

theorem p0Mat_inv_mul (y : Matrix (Fin ((t + 1) + 1)) (Fin 1) F)
    (hc : y (Fin.last (t + 1)) 0 ≠ 0) : p0InvMat y * p0Mat y = 1 := by
  apply blk_ext <;> intros <;>
    simp [mul_apply_index, p0Mat, p0InvMat, Matrix.one_apply, Finset.sum_ite_eq,
      Finset.sum_ite_eq', hc]

theorem kkMat_mul_inv (c : F) : kkMat (t := t) c * kkInvMat c = 1 := by
  apply blk_ext <;> intros <;>
    simp [mul_apply_index, kkMat, kkInvMat, Matrix.one_apply, Finset.sum_ite_eq']

theorem kkMat_inv_mul (c : F) : kkInvMat (t := t) c * kkMat c = 1 := by
  apply blk_ext <;> intros <;>
    simp [mul_apply_index, kkMat, kkInvMat, Matrix.one_apply, Finset.sum_ite_eq']

/-- `lower` of the column with only the last entry `c`, in block form. -/
def lowerLastMat (c : F) :
    Matrix (Fin ((0 + 1) + ((t + 1) + 1))) (Fin ((0 + 1) + ((t + 1) + 1))) F :=
  blk t 1 0 0 0 (fun j k => if j = k then 1 else 0) 0 c 0 1

theorem lowerMat_eq_of_last (y : Matrix (Fin ((t + 1) + 1)) (Fin 1) F) :
    lowerMat y = lowerZeroMat (Matrix.of fun j (_ : Fin 1) => y j.castSucc 0) *
      lowerLastMat (y (Fin.last (t + 1)) 0) := by
  apply blk_ext <;> intros <;>
    simp [mul_apply_index, lowerZeroMat, lowerLastMat, lowerMat, Finset.sum_ite_eq']

theorem lowerLastMat_mul_neg (c : F) : lowerLastMat (t := t) c * lowerLastMat (-c) = 1 := by
  apply blk_ext <;> intros <;>
    simp [mul_apply_index, lowerLastMat, Matrix.one_apply, Finset.sum_ite_eq']

end Identity

section GLElements

variable [Field F]

/-- The parabolic factor `p₀` as an invertible matrix. -/
def p0GL (y : Matrix (Fin ((t + 1) + 1)) (Fin 1) F) (hc : y (Fin.last (t + 1)) 0 ≠ 0) :
    Langlands.GeneralLinear ((0 + 1) + ((t + 1) + 1)) F :=
  ⟨p0Mat y, p0InvMat y, p0Mat_mul_inv y hc, p0Mat_inv_mul y hc⟩

/-- The factor `κ` as an invertible matrix. -/
def kkGL (c : F) : Langlands.GeneralLinear ((0 + 1) + ((t + 1) + 1)) F :=
  ⟨kkMat c, kkInvMat c, kkMat_mul_inv c, kkMat_inv_mul c⟩

/-- `lower` of the last coordinate as an invertible matrix. -/
def lowerLastGL (c : F) : Langlands.GeneralLinear ((0 + 1) + ((t + 1) + 1)) F :=
  ⟨lowerLastMat c, lowerLastMat (-c), lowerLastMat_mul_neg c, by
    simpa using lowerLastMat_mul_neg (t := t) (-c)⟩

/-- The embedding `g ↦ diag(g, 1)` of `GL_((0+1)+(t+1))` in `GL_((0+1)+((t+1)+1))`. -/
def embedHom : Langlands.GeneralLinear ((0 + 1) + (t + 1)) F →*
    Langlands.GeneralLinear ((0 + 1) + ((t + 1) + 1)) F :=
  (GeneralLinear.blockSum (n := (0 + 1) + (t + 1)) (m := 1)).comp (MonoidHom.inl _ _)

/-- The embedding `g ↦ diag(g, 1)`. -/
def embed (g : Langlands.GeneralLinear ((0 + 1) + (t + 1)) F) :
    Langlands.GeneralLinear ((0 + 1) + ((t + 1) + 1)) F :=
  embedHom g

theorem embed_eq (g : Langlands.GeneralLinear ((0 + 1) + (t + 1)) F) :
    embed g = GeneralLinear.blockSum (n := (0 + 1) + (t + 1)) (m := 1) (g, 1) := rfl

theorem embed_mul (g h : Langlands.GeneralLinear ((0 + 1) + (t + 1)) F) :
    embed (g * h) = embed g * embed h := map_mul embedHom g h

theorem embed_inv (g : Langlands.GeneralLinear ((0 + 1) + (t + 1)) F) :
    embed g⁻¹ = (embed g)⁻¹ := map_inv embedHom g

theorem aI_eq : aI t = Fin.castAdd 1 (Fin.castAdd (t + 1) (0 : Fin (0 + 1))) := by
  apply Fin.ext
  simp [aI]

theorem mI_eq (j : Fin (t + 1)) : mI t j = Fin.castAdd 1 (Fin.natAdd (0 + 1) j) := by
  apply Fin.ext
  simp [mI, cI]

theorem lI_eq : lI t = Fin.natAdd ((0 + 1) + (t + 1)) (0 : Fin 1) := by
  apply Fin.ext
  simp [lI, cI]

variable (g : Langlands.GeneralLinear ((0 + 1) + (t + 1)) F)

@[simp] theorem embed_aa : embed g (aI t) (aI t) =
    g (Fin.castAdd (t + 1) 0) (Fin.castAdd (t + 1) 0) := by
  rw [aI_eq, embed_eq, blockSum_apply_left]
@[simp] theorem embed_am (j : Fin (t + 1)) : embed g (aI t) (mI t j) =
    g (Fin.castAdd (t + 1) 0) (Fin.natAdd (0 + 1) j) := by
  rw [aI_eq, mI_eq, embed_eq, blockSum_apply_left]
@[simp] theorem embed_al : embed g (aI t) (lI t) = 0 := by
  rw [aI_eq, lI_eq, embed_eq, blockSum_apply_left_right]
@[simp] theorem embed_ma (j : Fin (t + 1)) : embed g (mI t j) (aI t) =
    g (Fin.natAdd (0 + 1) j) (Fin.castAdd (t + 1) 0) := by
  rw [aI_eq, mI_eq, embed_eq, blockSum_apply_left]
@[simp] theorem embed_mm (j k : Fin (t + 1)) : embed g (mI t j) (mI t k) =
    g (Fin.natAdd (0 + 1) j) (Fin.natAdd (0 + 1) k) := by
  rw [mI_eq, mI_eq, embed_eq, blockSum_apply_left]
@[simp] theorem embed_ml (j : Fin (t + 1)) : embed g (mI t j) (lI t) = 0 := by
  rw [mI_eq, lI_eq, embed_eq, blockSum_apply_left_right]
@[simp] theorem embed_la : embed g (lI t) (aI t) = 0 := by
  rw [aI_eq, lI_eq, embed_eq, blockSum_apply_right_left]
@[simp] theorem embed_lm (j : Fin (t + 1)) : embed g (lI t) (mI t j) = 0 := by
  rw [mI_eq, lI_eq, embed_eq, blockSum_apply_right_left]
@[simp] theorem embed_ll : embed g (lI t) (lI t) = 1 := by
  rw [lI_eq, embed_eq, blockSum_apply_right]
  rfl

theorem embed_lower_val (z : Matrix (Fin (t + 1)) (Fin 1) F) :
    (embed (lower (0 + 1) (t + 1) F z) : Matrix _ _ F) = lowerZeroMat z := by
  apply blk_ext <;> intros <;>
    simp [lowerZeroMat, lower_first_first, lower_first_second, lower_second_first,
      lower_second_second]

/-- **The decomposition** `lower(y) = p₀ · diag(lower(y'/c), 1) · κ`. -/
theorem lower_eq_p0GL_mul (y : Matrix (Fin ((t + 1) + 1)) (Fin 1) F)
    (hc : y (Fin.last (t + 1)) 0 ≠ 0) :
    lower (0 + 1) ((t + 1) + 1) F y = p0GL y hc * embed (lower (0 + 1) (t + 1) F
      (Matrix.of fun j (_ : Fin 1) => y j.castSucc 0 * (y (Fin.last (t + 1)) 0)⁻¹)) *
        kkGL (y (Fin.last (t + 1)) 0) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, embed_lower_val, lower_val_eq, lowerMat_eq y hc]
  rfl

/-- **The decomposition** `lower(y) = diag(lower(y'), 1) · lower(c e_last)`. -/
theorem lower_eq_embed_mul (y : Matrix (Fin ((t + 1) + 1)) (Fin 1) F) :
    lower (0 + 1) ((t + 1) + 1) F y = embed (lower (0 + 1) (t + 1) F
      (Matrix.of fun j (_ : Fin 1) => y j.castSucc 0)) * lowerLastGL (y (Fin.last (t + 1)) 0) := by
  apply Units.ext
  rw [Units.val_mul, embed_lower_val, lower_val_eq, lowerMat_eq_of_last y]
  rfl

end GLElements

end Langlands.Shahidi.OpenCell.Base
