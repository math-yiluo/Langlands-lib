import Langlands.Representation.Archimedean.RealInductionStagesAverage
import Langlands.Representation.Archimedean.RealBlockRotation
import Langlands.Representation.Archimedean.PrincipalSeriesExtension
import Langlands.Representation.Archimedean.RealStrictCharacterLanglandsQuotient

/-!
# Block embeddings and slices for induction in stages

For `a + r ≤ n`, `blockEmb` embeds `GL_r(ℝ)` into `GL_n(ℝ)` as the middle diagonal block
`h ↦ diag(1_a, h, 1_(n-a-r))`. For a function `F` on `GL_n(ℝ)` and `κ ∈ GL_n(ℝ)`, the slice
`slice n a r κ F` is the function `h ↦ ν(h) F(ι(h) κ)` on `GL_r(ℝ)`, where
`ν(h) = |det h|^(-c)` with `c = (n - r)/2 - a`.

If `F` lies in the real standard module of `pre ++ ds ++ post` with `realRank pre = a`,
`realRank ds = r` and `a + r + realRank post = n`, then every slice lies in the real standard
module of `ds`, and for `κ ∈ O(n)` the slices of `O(n)`-finite functions are `O(r)`-finite.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

namespace InductionStages

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

set_option backward.isDefEq.respectTransparency false

/-! ## The coordinate embedding -/

section Embedding

variable {n a r : ℕ}

/-- The coordinate `i` is one of the middle coordinates `a, …, a + r - 1`. -/
def IsMid (a r : ℕ) (i : Fin n) : Prop := a ≤ (i : ℕ) ∧ (i : ℕ) < a + r

instance (a r : ℕ) : DecidablePred (IsMid (n := n) a r) := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _))

/-- The middle coordinate `a + j`. -/
def idx (h : a + r ≤ n) (j : Fin r) : Fin n := ⟨a + j, by omega⟩

theorem idx_val (h : a + r ≤ n) (j : Fin r) : (idx h j : ℕ) = a + j := rfl

theorem isMid_idx (h : a + r ≤ n) (j : Fin r) : IsMid a r (idx h j) := by
  simp only [IsMid, idx_val]
  omega

theorem idx_injective (h : a + r ≤ n) : Function.Injective (idx h) := by
  intro j j' e
  have := congrArg Fin.val e
  simp only [idx_val] at this
  exact Fin.ext (by omega)

theorem exists_idx_of_isMid (h : a + r ≤ n) {i : Fin n} (hi : IsMid a r i) :
    ∃ j, i = idx h j :=
  ⟨⟨i - a, by unfold IsMid at hi; omega⟩, Fin.ext (by simp only [idx_val]; unfold IsMid at hi; omega)⟩

theorem not_isMid_iff_not_mem_range (h : a + r ≤ n) (i : Fin n) :
    ¬IsMid a r i ↔ i ∉ Set.range (idx h) := by
  constructor
  · rintro hi ⟨j, rfl⟩
    exact hi (isMid_idx h j)
  · intro hi hmid
    obtain ⟨j, rfl⟩ := exists_idx_of_isMid h hmid
    exact hi ⟨j, rfl⟩

/-- The `n × r` matrix of the coordinate embedding: `P i j = 1` iff `i = a + j`. -/
def embMat (n a r : ℕ) : Matrix (Fin n) (Fin r) ℝ :=
  Matrix.of fun i j => if (i : ℕ) = a + j then 1 else 0

theorem embMat_mul_apply_idx (h : a + r ≤ n) {m : Type*} (M : Matrix (Fin r) m ℝ)
    (k : Fin r) (l : m) : (embMat n a r * M) (idx h k) l = M k l := by
  rw [Matrix.mul_apply, Finset.sum_eq_single k]
  · simp [embMat, idx]
  · intro j _ hj
    have : ¬ ((k : ℕ) = j) := fun e => hj (Fin.ext e).symm
    simp [embMat, idx, this]
  · simp

theorem embMat_mul_apply_of_not_isMid {m : Type*} (M : Matrix (Fin r) m ℝ) {i : Fin n}
    (hi : ¬IsMid a r i) (l : m) : (embMat n a r * M) i l = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  have : ¬ ((i : ℕ) = a + j) := fun e => hi ⟨by omega, by omega⟩
  simp [embMat, this]

theorem mul_embMat_transpose_apply_idx (h : a + r ≤ n) {m : Type*} (M : Matrix m (Fin r) ℝ)
    (l : m) (k : Fin r) : (M * (embMat n a r)ᵀ) l (idx h k) = M l k := by
  rw [Matrix.mul_apply, Finset.sum_eq_single k]
  · simp [embMat, idx]
  · intro j _ hj
    have : ¬ ((k : ℕ) = j) := fun e => hj (Fin.ext e).symm
    simp [embMat, idx, this]
  · simp

theorem mul_embMat_transpose_apply_of_not_isMid {m : Type*} (M : Matrix m (Fin r) ℝ)
    (l : m) {i : Fin n} (hi : ¬IsMid a r i) : (M * (embMat n a r)ᵀ) l i = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  have : ¬ ((i : ℕ) = a + j) := fun e => hi ⟨by omega, by omega⟩
  simp [embMat, this]

/-- `Pᵀ P = 1`. -/
theorem embMat_transpose_mul_embMat (h : a + r ≤ n) :
    (embMat n a r)ᵀ * embMat n a r = 1 := by
  ext j l
  rw [Matrix.mul_apply, Finset.sum_eq_single (idx h j)]
  · simp only [Matrix.transpose_apply, embMat, Matrix.of_apply, idx_val,
      Matrix.one_apply]
    by_cases hjl : j = l
    · subst hjl; simp
    · have : ¬ ((j : ℕ) = l) := fun e => hjl (Fin.ext e)
      simp [this, hjl]
  · intro i _ hi
    have : ¬ ((i : ℕ) = a + j) := fun e => hi (Fin.ext (by simp only [idx_val]; omega))
    simp [embMat, this]
  · simp

/-- The block matrix `1 + P (y - 1) Pᵀ = diag(1_a, y, 1)`. -/
def blockMat (n a r : ℕ) (y : Matrix (Fin r) (Fin r) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1 + embMat n a r * (y - 1) * (embMat n a r)ᵀ

theorem blockMat_apply_idx (h : a + r ≤ n) (y : Matrix (Fin r) (Fin r) ℝ) (k l : Fin r) :
    blockMat n a r y (idx h k) (idx h l) = y k l := by
  simp only [blockMat, Matrix.add_apply, mul_embMat_transpose_apply_idx h,
    embMat_mul_apply_idx h, Matrix.sub_apply, Matrix.one_apply]
  by_cases hkl : k = l
  · subst hkl; simp
  · have : idx h k ≠ idx h l := fun e => hkl (idx_injective h e)
    simp [this, hkl]

theorem blockMat_apply_of_not_isMid_left (y : Matrix (Fin r) (Fin r) ℝ) {i : Fin n}
    (hi : ¬IsMid a r i) (j : Fin n) : blockMat n a r y i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
  simp only [blockMat, Matrix.add_apply, Matrix.mul_assoc]
  rw [embMat_mul_apply_of_not_isMid _ hi, add_zero]

theorem blockMat_apply_of_not_isMid_right (y : Matrix (Fin r) (Fin r) ℝ) (i : Fin n)
    {j : Fin n} (hj : ¬IsMid a r j) :
    blockMat n a r y i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
  simp only [blockMat, Matrix.add_apply]
  rw [mul_embMat_transpose_apply_of_not_isMid _ _ hj, add_zero]

theorem blockMat_one : blockMat n a r 1 = 1 := by
  simp [blockMat]

theorem blockMat_mul (h : a + r ≤ n) (y z : Matrix (Fin r) (Fin r) ℝ) :
    blockMat n a r (y * z) = blockMat n a r y * blockMat n a r z := by
  have hP := embMat_transpose_mul_embMat h
  have hyz : y * z - 1 = (y - 1) + (z - 1) + (y - 1) * (z - 1) := by noncomm_ring
  simp only [blockMat, hyz, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
  have key : embMat n a r * (y - 1) * (embMat n a r)ᵀ * (embMat n a r * (z - 1) *
      (embMat n a r)ᵀ) = embMat n a r * ((y - 1) * (z - 1)) * (embMat n a r)ᵀ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (embMat n a r)ᵀ (embMat n a r), hP, Matrix.one_mul]
  rw [key]
  abel

theorem blockMat_transpose (y : Matrix (Fin r) (Fin r) ℝ) :
    blockMat n a r yᵀ = (blockMat n a r y)ᵀ := by
  simp only [blockMat, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.transpose_sub, Matrix.mul_assoc]

/-- The embedding `h ↦ diag(1_a, h, 1)` of `GL_r(ℝ)` into `GL_n(ℝ)`. -/
def blockEmb (h : a + r ≤ n) : Langlands.GeneralLinear r ℝ →* Langlands.GeneralLinear n ℝ where
  toFun g :=
    { val := blockMat n a r (g : Matrix (Fin r) (Fin r) ℝ)
      inv := blockMat n a r ((g⁻¹ : Langlands.GeneralLinear r ℝ) : Matrix (Fin r) (Fin r) ℝ)
      val_inv := by rw [← blockMat_mul h, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        blockMat_one]
      inv_val := by rw [← blockMat_mul h, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        blockMat_one] }
  map_one' := Units.ext blockMat_one
  map_mul' g g' := Units.ext (blockMat_mul h _ _)

theorem blockEmb_val (h : a + r ≤ n) (g : Langlands.GeneralLinear r ℝ) :
    (blockEmb h g : Matrix (Fin n) (Fin n) ℝ) = blockMat n a r (g : Matrix (Fin r) (Fin r) ℝ) :=
  rfl

theorem blockEmb_mem_unitaryCompact (h : a + r ≤ n) {k : Langlands.GeneralLinear r ℝ}
    (hk : k ∈ unitaryCompact ℝ r) : blockEmb h k ∈ unitaryCompact ℝ n := by
  change blockMat n a r (k : Matrix (Fin r) (Fin r) ℝ) ∈ Matrix.unitaryGroup (Fin n) ℝ
  have hk' : (k : Matrix (Fin r) (Fin r) ℝ) ∈ Matrix.unitaryGroup (Fin r) ℝ := hk
  rw [Matrix.mem_unitaryGroup_iff'] at hk' ⊢
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at hk' ⊢
  rw [← blockMat_transpose, ← blockMat_mul h, hk', blockMat_one]

end Embedding

/-! ## Positions in concatenated lists -/

section Lists

open GramFormula

theorem realRank_append' (xs ys : List RealBlock) :
    realRank (xs ++ ys) = realRank xs + realRank ys := by
  simp [realRank, List.map_append, List.sum_append]

theorem rank_character (c : RealCharacterData) : (RealBlock.character c).rank = 1 := rfl

theorem rank_induced (d : ComplexCharacterData) : (RealBlock.induced d).rank = 2 := rfl

theorem realPositionCharacter_append_left : ∀ (pre M : List RealBlock) (k : ℕ),
    realPositionCharacter (pre ++ M) (realRank pre + k) = realPositionCharacter M k
  | [], M, k => by rw [List.nil_append, realRank_nil, zero_add]
  | .character c :: pre, M, k => by
      rw [List.cons_append, realRank_cons, rank_character,
        show 1 + realRank pre + k = (realRank pre + k) + 1 by omega]
      exact realPositionCharacter_append_left pre M k
  | .induced d :: pre, M, k => by
      rw [List.cons_append, realRank_cons, rank_induced,
        show 2 + realRank pre + k = (realRank pre + k) + 2 by omega]
      exact realPositionCharacter_append_left pre M k

theorem realPositionCharacter_append_right : ∀ (ds post : List RealBlock) (k : ℕ),
    k < realRank ds → realPositionCharacter (ds ++ post) k = realPositionCharacter ds k
  | [], _, k, hk => by simp at hk
  | .character _ :: _, _, 0, _ => rfl
  | .character _ :: ds, post, k + 1, hk => by
      rw [realRank_cons, rank_character] at hk
      exact realPositionCharacter_append_right ds post k (by omega)
  | .induced _ :: _, _, 0, _ => rfl
  | .induced _ :: _, _, 1, _ => rfl
  | .induced _ :: ds, post, k + 2, hk => by
      rw [realRank_cons, rank_induced] at hk
      exact realPositionCharacter_append_right ds post k (by omega)

theorem realPositionExponent_append_left : ∀ (pre M : List RealBlock) (k : ℕ),
    realPositionExponent (pre ++ M) (realRank pre + k) = realPositionExponent M k
  | [], M, k => by rw [List.nil_append, realRank_nil, zero_add]
  | .character c :: pre, M, k => by
      rw [List.cons_append, realRank_cons, rank_character,
        show 1 + realRank pre + k = (realRank pre + k) + 1 by omega]
      exact realPositionExponent_append_left pre M k
  | .induced d :: pre, M, k => by
      rw [List.cons_append, realRank_cons, rank_induced,
        show 2 + realRank pre + k = (realRank pre + k) + 2 by omega]
      exact realPositionExponent_append_left pre M k

theorem realPositionExponent_append_right : ∀ (ds post : List RealBlock) (k : ℕ),
    k < realRank ds → realPositionExponent (ds ++ post) k = realPositionExponent ds k
  | [], _, k, hk => by simp at hk
  | .character _ :: _, _, 0, _ => rfl
  | .character _ :: ds, post, k + 1, hk => by
      rw [realRank_cons, rank_character] at hk
      exact realPositionExponent_append_right ds post k (by omega)
  | .induced _ :: _, _, 0, _ => rfl
  | .induced _ :: _, _, 1, _ => rfl
  | .induced _ :: ds, post, k + 2, hk => by
      rw [realRank_cons, rank_induced] at hk
      exact realPositionExponent_append_right ds post k (by omega)

theorem realInducedBlockAt_append_left : ∀ (pre M : List RealBlock) (k : ℕ),
    realInducedBlockAt (pre ++ M) (realRank pre + k) = realInducedBlockAt M k
  | [], M, k => by rw [List.nil_append, realRank_nil, zero_add]
  | .character c :: pre, M, k => by
      rw [List.cons_append, realRank_cons, rank_character,
        show 1 + realRank pre + k = (realRank pre + k) + 1 by omega]
      exact realInducedBlockAt_append_left pre M k
  | .induced d :: pre, M, k => by
      rw [List.cons_append, realRank_cons, rank_induced,
        show 2 + realRank pre + k = (realRank pre + k) + 2 by omega]
      exact realInducedBlockAt_append_left pre M k

theorem realInducedBlockAt_append_right : ∀ (ds post : List RealBlock) (k : ℕ),
    k < realRank ds → realInducedBlockAt (ds ++ post) k = realInducedBlockAt ds k
  | [], _, k, hk => by simp at hk
  | .character _ :: _, _, 0, _ => rfl
  | .character _ :: ds, post, k + 1, hk => by
      rw [realRank_cons, rank_character] at hk
      exact realInducedBlockAt_append_right ds post k (by omega)
  | .induced _ :: _, _, 0, _ => rfl
  | .induced _ :: _, _, 1, _ => rfl
  | .induced _ :: ds, post, k + 2, hk => by
      rw [realRank_cons, rank_induced] at hk
      exact realInducedBlockAt_append_right ds post k (by omega)

/-- An induction block of `pre ++ M` lies inside `pre` or inside `M`. -/
theorem realInducedBlockAt_append_cases : ∀ (pre M : List RealBlock) (p : ℕ)
    (d : ComplexCharacterData), realInducedBlockAt (pre ++ M) p = some d →
      (p + 1 < realRank pre ∧ realInducedBlockAt pre p = some d) ∨
        (realRank pre ≤ p ∧ realInducedBlockAt M (p - realRank pre) = some d)
  | [], M, p, d, h => Or.inr ⟨by simp, by simpa using h⟩
  | .character _ :: _, _, 0, _, h => by simp [realInducedBlockAt] at h
  | .character c :: pre, M, p + 1, d, h => by
      rcases realInducedBlockAt_append_cases pre M p d h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        rw [realRank_cons, rank_character]
        exact ⟨by omega, h2⟩
      · right
        rw [realRank_cons, rank_character]
        refine ⟨by omega, ?_⟩
        rw [show p + 1 - (1 + realRank pre) = p - realRank pre by omega]
        exact h2
  | .induced e :: pre, M, 0, d, h => by
      left
      rw [realRank_cons, rank_induced]
      exact ⟨by omega, h⟩
  | .induced _ :: _, _, 1, _, h => by simp [realInducedBlockAt] at h
  | .induced e :: pre, M, p + 2, d, h => by
      rcases realInducedBlockAt_append_cases pre M p d h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        rw [realRank_cons, rank_induced]
        exact ⟨by omega, h2⟩
      · right
        rw [realRank_cons, rank_induced]
        refine ⟨by omega, ?_⟩
        rw [show p + 2 - (2 + realRank pre) = p - realRank pre by omega]
        exact h2

end Lists

/-! ## The factor `ν` -/

section Factor

variable {n a r : ℕ}

/-- The exponent `c = (n - r)/2 - a`. -/
def sliceExponent (n a r : ℕ) : ℂ := ((n : ℂ) - r) / 2 - a

/-- The factor `ν(g) = |det g|^(-c)` with `c = (n - r)/2 - a`. -/
def sliceFactor (n a r : ℕ) (g : Langlands.GeneralLinear r ℝ) : ℂ :=
  ((|(g : Matrix (Fin r) (Fin r) ℝ).det| : ℝ) : ℂ) ^ (-sliceExponent n a r)

theorem sliceFactor_mul (g g' : Langlands.GeneralLinear r ℝ) :
    sliceFactor n a r (g * g') = sliceFactor n a r g * sliceFactor n a r g' := by
  simp only [sliceFactor, Units.val_mul, Matrix.det_mul, abs_mul, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (abs_nonneg _) (abs_nonneg _) _

theorem sliceFactor_of_abs_det_eq_one {g : Langlands.GeneralLinear r ℝ}
    (hg : |(g : Matrix (Fin r) (Fin r) ℝ).det| = 1) : sliceFactor n a r g = 1 := by
  rw [sliceFactor, hg, Complex.ofReal_one, Complex.one_cpow]

theorem sliceFactor_one : sliceFactor n a r 1 = 1 :=
  sliceFactor_of_abs_det_eq_one (by simp)

theorem sliceFactor_of_mem_unitaryCompact {k : Langlands.GeneralLinear r ℝ}
    (hk : k ∈ unitaryCompact ℝ r) : sliceFactor n a r k = 1 := by
  refine sliceFactor_of_abs_det_eq_one ?_
  have h := Unitary.star_mul_self_of_mem (Matrix.det_of_mem_unitary hk)
  rw [star_trivial] at h
  rcases mul_self_eq_one_iff.mp h with h' | h' <;> rw [h'] <;> simp

theorem sliceFactor_of_mem_upperUnipotent {u : Langlands.GeneralLinear r ℝ}
    (hu : u ∈ Langlands.GeneralLinear.upperUnipotent r ℝ) : sliceFactor n a r u = 1 := by
  refine sliceFactor_of_abs_det_eq_one ?_
  rw [Matrix.det_of_isUpperTriangular hu.1, Finset.prod_eq_one fun i _ => hu.2 i, abs_one]

theorem cpow_prod_ofReal {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (c : ℂ) :
    ((∏ i ∈ s, f i : ℝ) : ℂ) ^ c = ∏ i ∈ s, ((f i : ℝ) : ℂ) ^ c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf j) (Finset.prod_nonneg fun i _ => hf i), ih]

theorem sliceFactor_diagonalUnits (t : Fin r → ℝˣ) :
    sliceFactor n a r (Iwasawa.diagonalUnits t) =
      ∏ j, ((|((t j : ℝˣ) : ℝ)| : ℝ) : ℂ) ^ (-sliceExponent n a r) := by
  rw [sliceFactor, Iwasawa.diagonalUnits_val, Matrix.det_diagonal, Finset.abs_prod]
  exact cpow_prod_ofReal _ _ (fun _ => abs_nonneg _) _

/-- `ν` is smooth on the invertible matrices. -/
theorem contDiffAt_sliceFactor {y : Matrix (Fin r) (Fin r) ℝ} (hy : IsUnit y) :
    ContDiffAt ℝ ∞ (fun y : Matrix (Fin r) (Fin r) ℝ => ((|y.det| : ℝ) : ℂ) ^
      (-sliceExponent n a r)) y := by
  have hdet : y.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det y).mp hy).ne_zero
  have hd : ContDiff ℝ ∞ (fun y : Matrix (Fin r) (Fin r) ℝ => y.det) :=
    PrincipalSeriesExtension.contDiff_det_comp fun p q =>
      PrincipalSeriesExtension.contDiff_entry p q
  have habs : ContDiffAt ℝ ∞ (fun y : Matrix (Fin r) (Fin r) ℝ => |y.det|) y :=
    (contDiffAt_abs hdet).comp y hd.contDiffAt
  exact PrincipalSeriesExtension.contDiffAt_ofReal_cpow habs (abs_pos.mpr hdet) _

end Factor

/-! ## The torus, the unipotent group and the rotations -/

section Torus

variable {n a r : ℕ}

/-- `t` on the middle coordinates and `1` elsewhere. -/
def extUnits (_h : a + r ≤ n) (t : Fin r → ℝˣ) : Fin n → ℝˣ := fun i =>
  if hi : IsMid a r i then t ⟨(i : ℕ) - a, by unfold IsMid at hi; omega⟩ else 1

theorem extUnits_idx (h : a + r ≤ n) (t : Fin r → ℝˣ) (j : Fin r) :
    extUnits h t (idx h j) = t j := by
  rw [extUnits, dite_eq_left (isMid_idx h j)]
  congr 1
  ext
  simp [idx_val]

theorem extUnits_of_not_isMid (h : a + r ≤ n) (t : Fin r → ℝˣ) {i : Fin n}
    (hi : ¬IsMid a r i) : extUnits h t i = 1 :=
  dite_eq_right hi

theorem blockEmb_diagonalUnits (h : a + r ≤ n) (t : Fin r → ℝˣ) :
    blockEmb h (Iwasawa.diagonalUnits t) = Iwasawa.diagonalUnits (extUnits h t) := by
  apply Units.ext
  ext i j
  rw [blockEmb_val, Iwasawa.diagonalUnits_val, Iwasawa.diagonalUnits_val, Matrix.diagonal_apply]
  by_cases hi : IsMid a r i
  · obtain ⟨k, rfl⟩ := exists_idx_of_isMid h hi
    by_cases hj : IsMid a r j
    · obtain ⟨l, rfl⟩ := exists_idx_of_isMid h hj
      rw [blockMat_apply_idx h, Matrix.diagonal_apply, extUnits_idx]
      simp only [(idx_injective h).eq_iff]
    · rw [blockMat_apply_of_not_isMid_right _ _ hj, Matrix.one_apply]
      have : idx h k ≠ j := fun e => hj (e ▸ isMid_idx h k)
      simp [this]
  · rw [blockMat_apply_of_not_isMid_left _ hi, Matrix.one_apply, extUnits_of_not_isMid h t hi]
    simp

theorem blockEmb_mem_upperUnipotent (h : a + r ≤ n) {u : Langlands.GeneralLinear r ℝ}
    (hu : u ∈ upperUnipotent r ℝ) : blockEmb h u ∈ upperUnipotent n ℝ := by
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · change blockMat n a r (u : Matrix (Fin r) (Fin r) ℝ) i j = 0
    simp only [id] at hji
    by_cases hi : IsMid a r i
    · obtain ⟨k, rfl⟩ := exists_idx_of_isMid h hi
      by_cases hj : IsMid a r j
      · obtain ⟨l, rfl⟩ := exists_idx_of_isMid h hj
        rw [blockMat_apply_idx h]
        refine hu.1 ?_
        simp only [id, Fin.lt_def, idx_val] at hji ⊢
        omega
      · rw [blockMat_apply_of_not_isMid_right _ _ hj, Matrix.one_apply_ne (ne_of_gt hji)]
    · rw [blockMat_apply_of_not_isMid_left _ hi, Matrix.one_apply_ne (ne_of_gt hji)]
  · change blockMat n a r (u : Matrix (Fin r) (Fin r) ℝ) i i = 1
    by_cases hi : IsMid a r i
    · obtain ⟨k, rfl⟩ := exists_idx_of_isMid h hi
      rw [blockMat_apply_idx h]
      exact hu.2 k
    · rw [blockMat_apply_of_not_isMid_left _ hi, Matrix.one_apply_eq]

/-- `ν(diag t) · χ_n(ext t) = χ_r(t)` when the characters of the middle positions of `χ` are
those of `ψ` and the other characters are trivial at `1`. -/
theorem sliceFactor_mul_principalSeriesCharacter (h : a + r ≤ n) {χ ψ : ℕ → ℝˣ → ℂ}
    (hχ : ∀ j : Fin r, χ (a + j) = ψ j) (h1 : ∀ i, χ i 1 = 1) (t : Fin r → ℝˣ) :
    sliceFactor n a r (Iwasawa.diagonalUnits t) *
        principalSeriesCharacter ℝ n χ (extUnits h t) = principalSeriesCharacter ℝ r ψ t := by
  have hP : principalSeriesCharacter ℝ n χ (extUnits h t) =
      ∏ j : Fin r, χ (a + j) (t j) *
        ((|((t j : ℝˣ) : ℝ)| : ℝ) : ℂ) ^ (((n : ℂ) - 1) / 2 - ((a + j : ℕ) : ℂ)) := by
    rw [principalSeriesCharacter]
    symm
    refine Fintype.prod_of_injective (idx h) (idx_injective h) _ _ (fun i hi => ?_)
      (fun j => ?_)
    · rw [extUnits_of_not_isMid h t ((not_isMid_iff_not_mem_range h i).mpr hi), h1]
      simp
    · rw [extUnits_idx, idx_val, Real.norm_eq_abs, Module.finrank_self, pow_one]
  rw [hP, sliceFactor_diagonalUnits, principalSeriesCharacter, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hx : ((|((t j : ℝˣ) : ℝ)| : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (abs_pos.mpr (t j).ne_zero).ne'
  rw [hχ j, Real.norm_eq_abs, Module.finrank_self, pow_one, mul_left_comm,
    ← Complex.cpow_add _ _ hx]
  congr 2
  simp only [sliceExponent]
  push_cast
  ring

/-- `ι(r_p(θ)) = r_{a+p}(θ)`. -/
theorem blockEmb_blockRotation (h : a + r ≤ n) {p : ℕ} (hp : p + 1 < r) (θ : ℝ) :
    blockEmb h (blockRotation r p θ) = blockRotation n (a + p) θ := by
  apply Units.ext
  ext i j
  rw [blockEmb_val, RealBlockRotation.blockRotation_apply (by omega : a + p + 1 < n)]
  by_cases hi : IsMid a r i
  · obtain ⟨k, rfl⟩ := exists_idx_of_isMid h hi
    by_cases hj : IsMid a r j
    · obtain ⟨l, rfl⟩ := exists_idx_of_isMid h hj
      rw [blockMat_apply_idx h, RealBlockRotation.blockRotation_apply hp]
      simp only [idx_val, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega)
    · rw [blockMat_apply_of_not_isMid_right _ _ hj, Matrix.one_apply]
      unfold IsMid at hj
      simp only [idx_val, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega)
  · rw [blockMat_apply_of_not_isMid_left _ hi, Matrix.one_apply]
    unfold IsMid at hi
    simp only [Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)

end Torus

/-! ## Slices -/

section Slice

variable {n a r : ℕ}

/-- The slice `σ_κ F : g ↦ ν(g) F(ι(g) κ)` at `κ` of a function `F` on `GL_n(ℝ)`. -/
def slice (h : a + r ≤ n) (κ : Langlands.GeneralLinear n ℝ) :
    (Langlands.GeneralLinear n ℝ → ℂ) →ₗ[ℂ] (Langlands.GeneralLinear r ℝ → ℂ) where
  toFun F g := sliceFactor n a r g * F (blockEmb h g * κ)
  map_add' F G := by
    funext g
    simp only [Pi.add_apply, mul_add]
  map_smul' c F := by
    funext g
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem slice_apply (h : a + r ≤ n) (κ : Langlands.GeneralLinear n ℝ)
    (F : Langlands.GeneralLinear n ℝ → ℂ) (g : Langlands.GeneralLinear r ℝ) :
    slice h κ F g = sliceFactor n a r g * F (blockEmb h g * κ) :=
  rfl

theorem slice_apply_one (h : a + r ≤ n) (κ : Langlands.GeneralLinear n ℝ)
    (F : Langlands.GeneralLinear n ℝ → ℂ) : slice h κ F 1 = F κ := by
  rw [slice_apply, sliceFactor_one, map_one, one_mul, one_mul]

/-- `σ_κ (R(κ') F) = σ_{κ κ'} F`. -/
theorem slice_translate (h : a + r ≤ n) (κ κ' : Langlands.GeneralLinear n ℝ)
    (F : Langlands.GeneralLinear n ℝ → ℂ) :
    slice h κ (fun x => F (x * κ')) = slice h (κ * κ') F := by
  funext g
  simp only [slice_apply, mul_assoc]

/-- `σ_κ F (g g₀) = ν(g₀) σ_{ι(g₀) κ} F (g)`. -/
theorem slice_mul_apply (h : a + r ≤ n) (κ : Langlands.GeneralLinear n ℝ)
    (F : Langlands.GeneralLinear n ℝ → ℂ) (g g₀ : Langlands.GeneralLinear r ℝ) :
    slice h κ F (g * g₀) = sliceFactor n a r g₀ * slice h (blockEmb h g₀ * κ) F g := by
  simp only [slice_apply, sliceFactor_mul, map_mul, mul_assoc]
  ring

/-- The affine map `y ↦ blockMat y * κ` is smooth. -/
theorem contDiff_blockMat_mul (κ : Matrix (Fin n) (Fin n) ℝ) :
    ContDiff ℝ ∞ (fun y : Matrix (Fin r) (Fin r) ℝ => blockMat n a r y * κ) := by
  let Lm : Matrix (Fin r) (Fin r) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    { toFun := fun y => embMat n a r * y * (embMat n a r)ᵀ * κ
      map_add' := fun y z => by simp only [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c y => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
  have heq : (fun y : Matrix (Fin r) (Fin r) ℝ => blockMat n a r y * κ) =
      fun y => (κ - embMat n a r * (embMat n a r)ᵀ * κ) + Lm y := by
    funext y
    simp only [blockMat, Lm, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.add_mul, Matrix.one_mul, Matrix.mul_one]
    abel
  rw [heq]
  exact contDiff_const.add (LinearMap.toContinuousLinearMap Lm).contDiff

theorem contMDiff_slice (h : a + r ≤ n) (κ : Langlands.GeneralLinear n ℝ)
    {F : Langlands.GeneralLinear n ℝ → ℂ} (hF : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ F) :
    ContMDiff (matrixModel ℝ r) 𝓘(ℝ, ℂ) ∞ (slice h κ F) := by
  refine contMDiff_of_contDiffOn (ψ := fun y => ((|y.det| : ℝ) : ℂ) ^ (-sliceExponent n a r) *
    unitsExtension F (blockMat n a r y * (κ : Matrix (Fin n) (Fin n) ℝ))) ?_ ?_
  · intro y hy
    refine ContDiffAt.contDiffWithinAt ?_
    refine (contDiffAt_sliceFactor hy).mul ?_
    have hu : IsUnit (blockMat n a r y * (κ : Matrix (Fin n) (Fin n) ℝ)) := by
      obtain ⟨g, rfl⟩ := hy
      exact ⟨blockEmb h g * κ, rfl⟩
    have hext := (contDiffOn_unitsExtension hF).contDiffAt
      (isOpen_setOf_isUnit_matrix.mem_nhds hu)
    exact hext.comp y (contDiff_blockMat_mul (κ : Matrix (Fin n) (Fin n) ℝ)).contDiffAt
  · intro g
    simp only [slice_apply, sliceFactor]
    rw [← blockEmb_val h g, ← Units.val_mul, unitsExtension_val]

theorem slice_mem_principalSeries (h : a + r ≤ n) {χ ψ : ℕ → ℝˣ → ℂ}
    (hχ : ∀ j : Fin r, χ (a + j) = ψ j) (h1 : ∀ i, χ i 1 = 1)
    (κ : Langlands.GeneralLinear n ℝ) {F : Langlands.GeneralLinear n ℝ → ℂ}
    (hF : F ∈ principalSeries ℝ n χ) : slice h κ F ∈ principalSeries ℝ r ψ := by
  refine ⟨contMDiff_slice h κ hF.1, fun t u g => ?_⟩
  have hu := blockEmb_mem_upperUnipotent h u.2
  have harg : blockEmb h ((Iwasawa.diagonalUnits t : Langlands.GeneralLinear r ℝ) *
      (u : Langlands.GeneralLinear r ℝ) * g) * κ =
      (Iwasawa.diagonalUnits (extUnits h t) : Langlands.GeneralLinear n ℝ) *
        ((⟨blockEmb h u, hu⟩ : upperUnipotent n ℝ) : Langlands.GeneralLinear n ℝ) *
        (blockEmb h g * κ) := by
    simp only [map_mul, blockEmb_diagonalUnits, mul_assoc]
  rw [slice_apply, slice_apply, harg, hF.2, sliceFactor_mul, sliceFactor_mul,
    sliceFactor_of_mem_upperUnipotent u.2, mul_one,
    ← sliceFactor_mul_principalSeriesCharacter h hχ h1 t]
  ring

/-- The Fourier coefficients of a slice along a middle rotation. -/
theorem blockFourierCoefficient_slice (h : a + r ≤ n) {p : ℕ} (hp : p + 1 < r) (k : ℤ)
    (κ : Langlands.GeneralLinear n ℝ) (F : Langlands.GeneralLinear n ℝ → ℂ)
    (g : Langlands.GeneralLinear r ℝ) :
    blockFourierCoefficient r p k (slice h κ F) g =
      sliceFactor n a r g * blockFourierCoefficient n (a + p) k F (blockEmb h g * κ) := by
  unfold blockFourierCoefficient
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [slice_apply, sliceFactor_mul,
    sliceFactor_of_mem_unitaryCompact (blockRotation_mem_unitaryCompact r p θ), one_mul, map_mul,
    blockEmb_blockRotation h hp, mul_assoc]

theorem slice_mem_realStandardModule {pre ds post : List RealBlock} (h : a + r ≤ n)
    (ha : realRank pre = a) (hr : realRank ds = r) (κ : Langlands.GeneralLinear n ℝ)
    {F : Langlands.GeneralLinear n ℝ → ℂ} (hF : F ∈ realStandardModule n (pre ++ ds ++ post)) :
    slice h κ F ∈ realStandardModule r ds := by
  subst ha hr
  refine ⟨slice_mem_principalSeries h (fun j => ?_) (RealStrictCharacterLanglandsQuotient.realPositionCharacter_one _) κ hF.1,
    fun p d hd k hk g => ?_⟩
  · have := j.isLt
    rw [realPositionCharacter_append_right _ _ _ (by rw [realRank_append']; omega),
      realPositionCharacter_append_left]
  · have hp := realInducedBlockAt_lt hd
    rw [blockFourierCoefficient_slice h hp, hF.2 (realRank pre + p) d ?_ k hk, mul_zero]
    rw [realInducedBlockAt_append_right _ _ _ (by rw [realRank_append']; omega),
      realInducedBlockAt_append_left, hd]

theorem slice_mem_kFiniteVectors (h : a + r ≤ n) {κ : Langlands.GeneralLinear n ℝ}
    (hκ : κ ∈ unitaryCompact ℝ n) {F : Langlands.GeneralLinear n ℝ → ℂ}
    (hF : F ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ))
      (unitaryCompact ℝ n)) :
    slice h κ F ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear r ℝ))
      (unitaryCompact ℝ r) := by
  rw [mem_kFiniteVectors_iff] at hF ⊢
  have hle : Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ r =>
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear r ℝ) (k : Langlands.GeneralLinear r ℝ)
        (slice h κ F)) ≤
      (Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ n =>
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
          (k : Langlands.GeneralLinear n ℝ) F)).map (slice h κ) := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    have hk : κ⁻¹ * blockEmb h (k : Langlands.GeneralLinear r ℝ) * κ ∈ unitaryCompact ℝ n :=
      mul_mem (mul_mem (inv_mem hκ) (blockEmb_mem_unitaryCompact h k.2)) hκ
    refine ⟨Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
      (κ⁻¹ * blockEmb h (k : Langlands.GeneralLinear r ℝ) * κ) F,
      Submodule.subset_span ⟨⟨_, hk⟩, rfl⟩, ?_⟩
    funext g
    change slice h κ (fun x => F (x * (κ⁻¹ * blockEmb h (k : Langlands.GeneralLinear r ℝ) * κ)))
      g = slice h κ F (g * k)
    rw [slice_translate, slice_mul_apply,
      sliceFactor_of_mem_unitaryCompact k.2, one_mul, slice_apply, slice_apply]
    congr 2
    group
  have := hF
  exact Submodule.finiteDimensional_of_le hle

theorem slice_mem_kFin {pre ds post : List RealBlock} (h : a + r ≤ n)
    (ha : realRank pre = a) (hr : realRank ds = r) {κ : Langlands.GeneralLinear n ℝ}
    (hκ : κ ∈ unitaryCompact ℝ n) {F : Langlands.GeneralLinear n ℝ → ℂ}
    (hF : F ∈ KFin n (pre ++ ds ++ post)) : slice h κ F ∈ KFin r ds :=
  ⟨slice_mem_realStandardModule h ha hr κ hF.1, slice_mem_kFiniteVectors h hκ hF.2⟩

/-- `ι` restricted to `O(r) → O(n)`. -/
def blockEmbK (h : a + r ≤ n) : unitaryCompact ℝ r →* unitaryCompact ℝ n :=
  ((blockEmb h).comp (unitaryCompact ℝ r).subtype).codRestrict _
    fun k => blockEmb_mem_unitaryCompact h k.2

theorem coe_blockEmbK (h : a + r ≤ n) (k : unitaryCompact ℝ r) :
    ((blockEmbK h k : unitaryCompact ℝ n) : Langlands.GeneralLinear n ℝ) =
      blockEmb h (k : Langlands.GeneralLinear r ℝ) :=
  rfl

/-- The slice at `κ ∈ O(n)` as a linear map between `O(n)`- and `O(r)`-finite functions. -/
def sliceK {pre ds post : List RealBlock} (h : a + r ≤ n) (ha : realRank pre = a)
    (hr : realRank ds = r) (κ : unitaryCompact ℝ n) :
    KFin n (pre ++ ds ++ post) →ₗ[ℂ] KFin r ds :=
  ((slice h (κ : Langlands.GeneralLinear n ℝ)).comp (KFin n (pre ++ ds ++ post)).subtype).codRestrict
    _ fun F => slice_mem_kFin h ha hr κ.2 F.2

variable {pre ds post : List RealBlock}

theorem sliceK_apply_coe (h : a + r ≤ n) (ha : realRank pre = a) (hr : realRank ds = r)
    (κ : unitaryCompact ℝ n) (F : KFin n (pre ++ ds ++ post)) :
    ((sliceK h ha hr κ F : KFin r ds) : Langlands.GeneralLinear r ℝ → ℂ) =
      slice h (κ : Langlands.GeneralLinear n ℝ) (F : Langlands.GeneralLinear n ℝ → ℂ) :=
  rfl

theorem sliceK_apply_one (h : a + r ≤ n) (ha : realRank pre = a) (hr : realRank ds = r)
    (κ : unitaryCompact ℝ n) (F : KFin n (pre ++ ds ++ post)) :
    ((sliceK h ha hr κ F : KFin r ds) : Langlands.GeneralLinear r ℝ → ℂ) 1 =
      (F : Langlands.GeneralLinear n ℝ → ℂ) κ :=
  slice_apply_one h _ _

/-- `σ_κ (R(κ') F) = σ_{κ κ'} F`. -/
theorem sliceK_kRep (h : a + r ≤ n) (ha : realRank pre = a) (hr : realRank ds = r)
    (κ κ' : unitaryCompact ℝ n) (F : KFin n (pre ++ ds ++ post)) :
    sliceK h ha hr κ (kRep n (pre ++ ds ++ post) κ' F) = sliceK h ha hr (κ * κ') F := by
  apply Subtype.ext
  rw [sliceK_apply_coe, sliceK_apply_coe]
  have : ((kRep n (pre ++ ds ++ post) κ' F : KFin n (pre ++ ds ++ post)) :
      Langlands.GeneralLinear n ℝ → ℂ) =
      fun x => (F : Langlands.GeneralLinear n ℝ → ℂ) (x * κ') := by
    funext x
    exact kRep_apply_coe _ _ _ _ _
  rw [this, slice_translate]
  rfl

/-- `R(k) σ_κ F = σ_{ι(k) κ} F` for `k ∈ O(r)`. -/
theorem kRep_sliceK (h : a + r ≤ n) (ha : realRank pre = a) (hr : realRank ds = r)
    (κ : unitaryCompact ℝ n) (k : unitaryCompact ℝ r) (F : KFin n (pre ++ ds ++ post)) :
    kRep r ds k (sliceK h ha hr κ F) = sliceK h ha hr (blockEmbK h k * κ) F := by
  apply Subtype.ext
  funext g
  rw [kRep_apply_coe, sliceK_apply_coe, sliceK_apply_coe, slice_mul_apply,
    sliceFactor_of_mem_unitaryCompact k.2, one_mul]
  rfl

end Slice



end InductionStages

end Langlands.Archimedean
