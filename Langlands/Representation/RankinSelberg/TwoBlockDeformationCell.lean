import Langlands.Representation.RankinSelberg.TwoBlockJacquetData
import Langlands.Representation.Whittaker.GeneralLinear
import Langlands.Representation.Whittaker.TwoBlockCellUnipotentStabilityProof
import Langlands.Group.GL.TriangularParabolic
import Langlands.Representation.Shahidi.IntertwiningCovariance
import Langlands.Representation.Induction.CompactQuotientProof

/-!
# The upper radical of the lower two-block induction

For the lower two-block induction `I(σ_1 ⊗ σ_2)` of `GL_(t+1)` with blocks of sizes
`m 0 + 1` and `m 1 + 1`, and the complementary upper radical `u(x) = [[1, x], [0, 1]]`,
this module proves the block factorization `u(x) n = diag(n_0, n_1) u(n_0⁻¹ (β + x n_1))`
of an upper unipotent matrix `n` with diagonal blocks `n_0, n_1` and upper-right block
`β`, the corresponding decomposition of the first-superdiagonal sum, and the
consequences for sections: the subspace of sections whose restriction to the upper
radical has compact support is stable under the upper unipotent group, and the
scalar integral `f ↦ ∫ ⟨f(u(x)), ⊗ λ_i⟩ ψ(x_(m 0, 0)) dx` is `ψ⁻¹`-equivariant for
block functionals `λ_i` equivariant for the inverse standard characters.
-/

noncomputable section

open MeasureTheory

namespace Langlands.RankinSelberg.TwoBlockDeformation

open GeneralLinear TwoBlockJacquet Whittaker HarmonicAnalysis

universe uF uW uR

section Matrix

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) {R : Type uR} [CommRing R]

theorem val_index_zero (a : Fin (m 0 + 1)) : ((succBlockShape m h).index 0 a : ℕ) = a := by
  rw [index_zero h a]
  rfl

theorem val_index_one (b : Fin (m 1 + 1)) :
    ((succBlockShape m h).index 1 b : ℕ) = m 0 + 1 + b := by
  rw [index_one h b]
  rfl

/-- A sum over all coordinates splits into the two blocks. -/
theorem sum_index {M : Type*} [AddCommMonoid M] (f : Fin (t + 1) → M) :
    ∑ k, f k = ∑ c : Fin (m 0 + 1), f ((succBlockShape m h).index 0 c) +
      ∑ c : Fin (m 1 + 1), f ((succBlockShape m h).index 1 c) := by
  rw [← (succBlockShape m h).indexEquiv.sum_comp, Fintype.sum_sigma]
  exact Fin.sum_univ_two _

/-- Matrix multiplication in block coordinates. -/
theorem mul_apply_index (A C : GeneralLinear (t + 1) R) (k l : Fin (t + 1)) :
    (A * C) k l =
      ∑ c : Fin (m 0 + 1), A k ((succBlockShape m h).index 0 c) *
          C ((succBlockShape m h).index 0 c) l +
        ∑ c : Fin (m 1 + 1), A k ((succBlockShape m h).index 1 c) *
          C ((succBlockShape m h).index 1 c) l := by
  rw [Units.val_mul, Matrix.mul_apply]
  exact sum_index h _

/-- Equality of matrices is checked on the four blocks. -/
theorem ext_index {A C : GeneralLinear (t + 1) R}
    (h00 : ∀ (a b : Fin (m 0 + 1)),
      A ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 0 b) =
        C ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 0 b))
    (h01 : ∀ (a : Fin (m 0 + 1)) (b : Fin (m 1 + 1)),
      A ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 1 b) =
        C ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 1 b))
    (h10 : ∀ (a : Fin (m 1 + 1)) (b : Fin (m 0 + 1)),
      A ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 0 b) =
        C ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 0 b))
    (h11 : ∀ (a b : Fin (m 1 + 1)),
      A ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 1 b) =
        C ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 1 b)) :
    A = C := by
  apply Units.ext
  ext k l
  obtain ⟨⟨i, a⟩, rfl⟩ := (succBlockShape m h).indexEquiv.surjective k
  obtain ⟨⟨j, b⟩, rfl⟩ := (succBlockShape m h).indexEquiv.surjective l
  change A ((succBlockShape m h).index i a) ((succBlockShape m h).index j b) =
    C ((succBlockShape m h).index i a) ((succBlockShape m h).index j b)
  match i, a, j, b with
  | 0, a, 0, b => exact h00 a b
  | 0, a, 1, b => exact h01 a b
  | 1, a, 0, b => exact h10 a b
  | 1, a, 1, b => exact h11 a b

@[simp]
theorem leviEmbedding_index_zero_one (L : (succBlockShape m h).Levi R)
    (a : Fin (m 0 + 1)) (b : Fin (m 1 + 1)) :
    (succBlockShape m h).leviEmbedding R L ((succBlockShape m h).index 0 a)
      ((succBlockShape m h).index 1 b) = 0 :=
  (succBlockShape m h).leviEmbedding_apply_ne R L a b (show (0 : Fin 2) ≠ 1 by decide)

@[simp]
theorem leviEmbedding_index_one_zero (L : (succBlockShape m h).Levi R)
    (a : Fin (m 1 + 1)) (b : Fin (m 0 + 1)) :
    (succBlockShape m h).leviEmbedding R L ((succBlockShape m h).index 1 a)
      ((succBlockShape m h).index 0 b) = 0 :=
  (succBlockShape m h).leviEmbedding_apply_ne R L a b (show (1 : Fin 2) ≠ 0 by decide)

/-- Entries of an upper unipotent matrix from the second block to the first vanish. -/
theorem upperUnipotent_index_one_zero (n : upperUnipotent (t + 1) R)
    (a : Fin (m 1 + 1)) (b : Fin (m 0 + 1)) :
    n.val ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 0 b) = 0 :=
  UpperUnipotent.entry_eq_zero n
    ((succBlockShape m h).index_lt_index_of_block_lt (show (0 : Fin 2) < 1 by decide) b a)

section BlockSums

variable (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R)

theorem sum_radical_zero_zero_mul (f : Fin (m 0 + 1) → R) (a : Fin (m 0 + 1)) :
    ∑ c, upperRadical h R x ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 0 c) *
      f c = f a := by
  rw [Fintype.sum_eq_single a, upperRadical_index_zero_zero]
  · simp
  · intro c hc
    rw [upperRadical_index_zero_zero]
    simp [Ne.symm hc]

theorem sum_mul_radical_zero_zero (f : Fin (m 0 + 1) → R) (b : Fin (m 0 + 1)) :
    ∑ c, f c *
      upperRadical h R x ((succBlockShape m h).index 0 c) ((succBlockShape m h).index 0 b) =
      f b := by
  rw [Fintype.sum_eq_single b, upperRadical_index_zero_zero]
  · simp
  · intro c hc
    rw [upperRadical_index_zero_zero]
    simp [hc]

theorem sum_radical_one_one_mul (f : Fin (m 1 + 1) → R) (a : Fin (m 1 + 1)) :
    ∑ c, upperRadical h R x ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 1 c) *
      f c = f a := by
  rw [Fintype.sum_eq_single a, upperRadical_index_one_one]
  · simp
  · intro c hc
    rw [upperRadical_index_one_one]
    simp [Ne.symm hc]

theorem sum_mul_radical_one_one (f : Fin (m 1 + 1) → R) (b : Fin (m 1 + 1)) :
    ∑ c, f c *
      upperRadical h R x ((succBlockShape m h).index 1 c) ((succBlockShape m h).index 1 b) =
      f b := by
  rw [Fintype.sum_eq_single b, upperRadical_index_one_one]
  · simp
  · intro c hc
    rw [upperRadical_index_one_one]
    simp [hc]

theorem sum_radical_zero_one_mul (f : Fin (m 1 + 1) → R) (a : Fin (m 0 + 1)) :
    ∑ c, upperRadical h R x ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 1 c) *
      f c = ∑ c, x a c * f c :=
  Finset.sum_congr rfl fun c _ => by rw [upperRadical_index_zero_one]

theorem sum_mul_radical_zero_one (f : Fin (m 0 + 1) → R) (b : Fin (m 1 + 1)) :
    ∑ c, f c *
      upperRadical h R x ((succBlockShape m h).index 0 c) ((succBlockShape m h).index 1 b) =
      ∑ c, f c * x c b :=
  Finset.sum_congr rfl fun c _ => by rw [upperRadical_index_zero_one]

theorem sum_radical_one_zero_mul (f : Fin (m 0 + 1) → R) (a : Fin (m 1 + 1)) :
    ∑ c, upperRadical h R x ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 0 c) *
      f c = 0 :=
  Finset.sum_eq_zero fun c _ => by rw [upperRadical_index_one_zero, zero_mul]

theorem sum_mul_radical_one_zero (f : Fin (m 1 + 1) → R) (b : Fin (m 0 + 1)) :
    ∑ c, f c *
      upperRadical h R x ((succBlockShape m h).index 1 c) ((succBlockShape m h).index 0 b) =
      0 :=
  Finset.sum_eq_zero fun c _ => by rw [upperRadical_index_one_zero, mul_zero]

theorem sum_levi_zero_one_mul (L : (succBlockShape m h).Levi R) (f : Fin (m 1 + 1) → R)
    (a : Fin (m 0 + 1)) :
    ∑ c, (succBlockShape m h).leviEmbedding R L ((succBlockShape m h).index 0 a)
      ((succBlockShape m h).index 1 c) * f c = 0 :=
  Finset.sum_eq_zero fun c _ => by rw [leviEmbedding_index_zero_one, zero_mul]

theorem sum_levi_one_zero_mul (L : (succBlockShape m h).Levi R) (f : Fin (m 0 + 1) → R)
    (a : Fin (m 1 + 1)) :
    ∑ c, (succBlockShape m h).leviEmbedding R L ((succBlockShape m h).index 1 a)
      ((succBlockShape m h).index 0 c) * f c = 0 :=
  Finset.sum_eq_zero fun c _ => by rw [leviEmbedding_index_one_zero, zero_mul]

theorem sum_mul_unipotent_one_zero (n : upperUnipotent (t + 1) R) (f : Fin (m 1 + 1) → R)
    (b : Fin (m 0 + 1)) :
    ∑ c, f c * n.val ((succBlockShape m h).index 1 c) ((succBlockShape m h).index 0 b) = 0 :=
  Finset.sum_eq_zero fun c _ => by rw [upperUnipotent_index_one_zero, mul_zero]

end BlockSums

/-- The diagonal blocks `(n_0, n_1)` of an upper unipotent matrix, as a Levi element. -/
def unipotentLevi (n : upperUnipotent (t + 1) R) : (succBlockShape m h).Levi R :=
  (succBlockShape m h).leviProjection R
    ⟨n.val, (succBlockShape m h).mem_parabolic_of_isUpperTriangular n.val n.property.1⟩

@[simp]
theorem unipotentLevi_apply (n : upperUnipotent (t + 1) R) (i : Fin 2) (a b : Fin (m i + 1)) :
    unipotentLevi h n i a b =
      n.val ((succBlockShape m h).index i a) ((succBlockShape m h).index i b) :=
  rfl

/-- Each diagonal block of an upper unipotent matrix is upper unipotent. -/
theorem unipotentLevi_mem (n : upperUnipotent (t + 1) R) (i : Fin 2) :
    unipotentLevi h n i ∈ upperUnipotent (m i + 1) R := by
  have hmono : ∀ a b : Fin (m i + 1), b < a →
      (succBlockShape m h).index i b < (succBlockShape m h).index i a := by
    intro a b hab
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · rw [Fin.lt_def, val_index_zero, val_index_zero]
      exact hab
    · rw [Fin.lt_def, val_index_one, val_index_one]
      have : (b : ℕ) < a := hab
      omega
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · change n.val ((succBlockShape m h).index i a) ((succBlockShape m h).index i b) = 0
    exact UpperUnipotent.entry_eq_zero n (hmono a b hab)
  · change n.val ((succBlockShape m h).index i a) ((succBlockShape m h).index i a) = 1
    exact UpperUnipotent.entry_diag n _

/-- The upper-right block `β` of a matrix of total rank `t + 1`. -/
def unipotentCorner (n : upperUnipotent (t + 1) R) :
    Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R :=
  fun a b => n.val ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 1 b)

/-- The coordinate change `x ↦ n_0⁻¹ (β + x n_1)` attached to `n`. -/
def unipotentShift (n : upperUnipotent (t + 1) R)
    (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R) :
    Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R :=
  ((unipotentLevi h n 0)⁻¹ : GeneralLinear (m 0 + 1) R).val *
    (unipotentCorner h n + x * (unipotentLevi h n 1).val)

/-- Block factorization `u(x) n = diag(n_0, n_1) u(n_0⁻¹ (β + x n_1))`. -/
theorem upperRadical_mul_upperUnipotent (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R)
    (n : upperUnipotent (t + 1) R) :
    upperRadical h R x * n.val =
      (succBlockShape m h).leviEmbedding R (unipotentLevi h n) *
        upperRadical h R (unipotentShift h n x) := by
  have hshift : (unipotentLevi h n 0).val * unipotentShift h n x =
      unipotentCorner h n + x * (unipotentLevi h n 1).val := by
    rw [unipotentShift, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  apply ext_index h
  · intro a b
    rw [mul_apply_index h, mul_apply_index h, sum_radical_zero_zero_mul,
      sum_mul_unipotent_one_zero, sum_mul_radical_zero_zero, sum_levi_zero_one_mul, add_zero,
      add_zero, (succBlockShape m h).leviEmbedding_apply_same]
    rfl
  · intro a b
    have hab := congrFun (congrFun hshift a) b
    rw [Matrix.mul_apply, Matrix.add_apply, Matrix.mul_apply] at hab
    rw [mul_apply_index h, mul_apply_index h, sum_radical_zero_zero_mul,
      sum_radical_zero_one_mul, sum_mul_radical_zero_one, sum_levi_zero_one_mul, add_zero]
    calc _ = unipotentCorner h n a b + ∑ c, x a c * (unipotentLevi h n 1).val c b := rfl
      _ = ∑ c, (unipotentLevi h n 0).val a c * unipotentShift h n x c b := hab.symm
      _ = _ := Finset.sum_congr rfl fun c _ => by
          rw [(succBlockShape m h).leviEmbedding_apply_same]
  · intro a b
    rw [mul_apply_index h, mul_apply_index h, sum_radical_one_zero_mul, sum_radical_one_one_mul,
      upperUnipotent_index_one_zero, sum_levi_one_zero_mul, sum_mul_radical_one_zero]
  · intro a b
    rw [mul_apply_index h, mul_apply_index h, sum_radical_one_zero_mul, sum_radical_one_one_mul,
      sum_levi_one_zero_mul, sum_mul_radical_one_one, (succBlockShape m h).leviEmbedding_apply_same]
    rfl

/-- The first-superdiagonal sum splits into the two blocks and the corner entry. -/
theorem sum_superdiagonal_index (A : Matrix (Fin (t + 1)) (Fin (t + 1)) R) :
    ∑ k : Fin t, A k.castSucc k.succ =
      ∑ k : Fin (m 0), A ((succBlockShape m h).index 0 k.castSucc)
          ((succBlockShape m h).index 0 k.succ) +
        A ((succBlockShape m h).index 0 (Fin.last (m 0))) ((succBlockShape m h).index 1 0) +
        ∑ k : Fin (m 1), A ((succBlockShape m h).index 1 k.castSucc)
          ((succBlockShape m h).index 1 k.succ) := by
  obtain rfl : t = m 0 + 1 + m 1 := by
    have := blockRanks_add h
    omega
  rw [Fin.sum_univ_add, Fin.sum_univ_castSucc]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (Finset.sum_congr rfl fun k _ => ?_) ?_)
    (Finset.sum_congr rfl fun k _ => ?_)
  · congr 1 <;> apply Fin.ext <;> rw [val_index_zero] <;> simp
  · congr 1
    apply Fin.ext
    rw [val_index_zero]
    simp
  · congr 1

/-- The last row of an upper unipotent matrix is the last unit row. -/
theorem upperUnipotent_mul_apply_last {a b : ℕ} (A : upperUnipotent (a + 1) R)
    (x : Matrix (Fin (a + 1)) (Fin b) R) (j : Fin b) :
    (A.val.val * x) (Fin.last a) j = x (Fin.last a) j := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single (Fin.last a)]
  · rw [show A.val.val (Fin.last a) (Fin.last a) = 1 from UpperUnipotent.entry_diag A _, one_mul]
  · intro c hc
    rw [show A.val.val (Fin.last a) c = 0 from
      UpperUnipotent.entry_eq_zero A (lt_of_le_of_ne (Fin.le_last c) hc), zero_mul]

/-- The first column of an upper unipotent matrix is the first unit column. -/
theorem mul_upperUnipotent_apply_zero {a b : ℕ} (x : Matrix (Fin a) (Fin (b + 1)) R)
    (C : upperUnipotent (b + 1) R) (i : Fin a) :
    (x * C.val.val) i 0 = x i 0 := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single 0]
  · rw [show C.val.val 0 0 = 1 from UpperUnipotent.entry_diag C _, mul_one]
  · intro c hc
    rw [show C.val.val c 0 = 0 from
      UpperUnipotent.entry_eq_zero C (lt_of_le_of_ne (Fin.zero_le c) (Ne.symm hc)), mul_zero]

/-- The corner entry of the shifted coordinate. -/
theorem unipotentShift_last_zero (n : upperUnipotent (t + 1) R)
    (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R) :
    unipotentShift h n x (Fin.last (m 0)) 0 =
      unipotentCorner h n (Fin.last (m 0)) 0 + x (Fin.last (m 0)) 0 := by
  let A : upperUnipotent (m 0 + 1) R := ⟨_, (upperUnipotent (m 0 + 1) R).inv_mem
    (unipotentLevi_mem h n 0)⟩
  let C : upperUnipotent (m 1 + 1) R := ⟨_, unipotentLevi_mem h n 1⟩
  have h1 := upperUnipotent_mul_apply_last A (unipotentCorner h n + x * (unipotentLevi h n 1).val)
    0
  have h2 := mul_upperUnipotent_apply_zero x C (Fin.last (m 0))
  have hA : ((unipotentLevi h n 0)⁻¹ : GeneralLinear (m 0 + 1) R).val = A.val.val := rfl
  have hC : (unipotentLevi h n 1).val = C.val.val := rfl
  rw [unipotentShift, hA, h1, Matrix.add_apply, hC, h2]

end Matrix

section Sections

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))

/-- An upper unipotent matrix has determinant norm one. -/
theorem determinantNorm_eq_one_of_mem_upperUnipotent (T : F.TopologicalData) {n : ℕ}
    {g : GeneralLinear n F.Carrier} (hg : g ∈ upperUnipotent n F.Carrier) :
    T.determinantNorm n g = 1 := by
  have hdet : GeneralLinear.determinant g = 1 := Units.ext (by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one,
      Matrix.det_of_isUpperTriangular hg.1, Finset.prod_eq_one fun i _ => hg.2 i])
  change T.normalizedAbsUnits (GeneralLinear.determinant g) = 1
  rw [hdet, map_one]

/-- The block modulus is trivial on Levi elements whose blocks have determinant norm one. -/
theorem leviModulus_eq_one (T : F.TopologicalData) (L : (succBlockShape m h).Levi F.Carrier)
    (hL : ∀ i, T.determinantNorm (m i + 1) (L i) = 1) :
    T.leviModulus (succBlockShape m h) L = 1 := by
  rw [T.leviModulus_apply]
  exact Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => by
    change T.determinantNorm (m i + 1) (L i) ^ (m j + 1) /
      T.determinantNorm (m j + 1) (L j) ^ (m i + 1) = 1
    rw [hL i, hL j, one_pow, one_pow, div_one]

/-- Left translation by a Levi element with determinant-norm-one blocks acts on values by
the block tensor representation. -/
theorem sectionEval_leviEmbedding_mul (f : Sections F h σ)
    (L : (succBlockShape m h).Levi F.Carrier)
    (hL : ∀ i, F.canonicalTopologicalData.determinantNorm (m i + 1) (L i) = 1)
    (g : GeneralLinear (t + 1) F.Carrier) :
    sectionEval F h σ f ((succBlockShape m h).leviEmbedding F.Carrier L * g) =
      (succBlockShape m h).blockTensor σ L (sectionEval F h σ f g) := by
  have hcov := F.canonicalTopologicalData.normalizedOppositeParabolicInduced_covariant
    (succBlockShape m h) ((succBlockShape m h).blockTensor σ) f
    ((succBlockShape m h).oppositeLeviInParabolic F.Carrier L) g
  rw [BlockShape.oppositeLeviInParabolic_val, BlockShape.oppositeLeviProjection_section,
    leviModulus_eq_one F h _ L hL] at hcov
  rw [sectionEval, hcov]
  simp

/-- The restriction `x ↦ f(u(x))` of a section to the upper radical. -/
def radicalRestriction (f : Sections F h σ) (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier) :
    PiTensorProduct ℂ W :=
  sectionEval F h σ f (upperRadical h F.Carrier x)

/-- An upper unipotent translate restricts through the block factorization. -/
theorem radicalRestriction_inducedRep (n : upperUnipotent (t + 1) F.Carrier)
    (f : Sections F h σ) (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier) :
    radicalRestriction F h σ (inducedRep F h σ n f) x =
      (succBlockShape m h).blockTensor σ (unipotentLevi h n)
        (radicalRestriction F h σ f (unipotentShift h n x)) := by
  change sectionEval F h σ f (upperRadical h F.Carrier x * n.val) = _
  rw [upperRadical_mul_upperUnipotent, sectionEval_leviEmbedding_mul]
  · rfl
  · exact fun i => determinantNorm_eq_one_of_mem_upperUnipotent F _ (unipotentLevi_mem h n i)

/-- The sections whose restriction to the upper radical has compact support. -/
def compactRadicalSubmodule : Submodule ℂ (Sections F h σ) where
  carrier := {f | letI := F.canonicalTopologicalData.topology
    HasCompactSupport (radicalRestriction F h σ f)}
  zero_mem' := by
    let := F.canonicalTopologicalData.topology
    change HasCompactSupport (fun x => sectionEval F h σ 0 (upperRadical h F.Carrier x))
    simp only [sectionEval_zero]
    exact HasCompactSupport.zero
  add_mem' := by
    let := F.canonicalTopologicalData.topology
    intro f f' hf hf'
    exact HasCompactSupport.add hf hf'
  smul_mem' := by
    let := F.canonicalTopologicalData.topology
    intro c f hf
    exact hf.mono (Function.support_const_smul_subset c _)

theorem mem_compactRadicalSubmodule (f : Sections F h σ) :
    f ∈ compactRadicalSubmodule F h σ ↔
      letI := F.canonicalTopologicalData.topology
      HasCompactSupport (radicalRestriction F h σ f) :=
  Iff.rfl

/-- The compact-radical sections are stable under the upper unipotent group. -/
theorem inducedRep_mem_compactRadicalSubmodule (n : upperUnipotent (t + 1) F.Carrier)
    {f : Sections F h σ} (hf : f ∈ compactRadicalSubmodule F h σ) :
    inducedRep F h σ n f ∈ compactRadicalSubmodule F h σ := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let φ := affineHomeomorph F.Carrier (unipotentLevi h n 0) (unipotentCorner h n)
    (unipotentLevi h n 1)
  have hfun : radicalRestriction F h σ (inducedRep F h σ n f) =
      (succBlockShape m h).blockTensor σ (unipotentLevi h n) ∘
        (radicalRestriction F h σ f ∘ φ) := by
    funext x
    exact radicalRestriction_inducedRep F h σ n f x
  rw [mem_compactRadicalSubmodule, hfun]
  exact (HasCompactSupport.comp_homeomorph hf φ).comp_left (map_zero _)

section Contraction

variable (ψ : letI := F.canonicalTopologicalData.topology
  HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier)

/-- Block functionals equivariant for the inverse standard characters scale the
contraction of a unipotent block translate by the product of the block characters. -/
theorem tensorContraction_blockTensor (ell : ∀ i, W i →ₗ[ℂ] ℂ)
    (hell : ∀ i, letI := F.canonicalTopologicalData.topology
      ell i ∈ glInverseFunctionals ψ (m i) (σ i))
    (L : (succBlockShape m h).Levi F.Carrier) (hL : ∀ i, L i ∈ upperUnipotent (m i + 1) F.Carrier)
    (v : PiTensorProduct ℂ W) :
    letI := F.canonicalTopologicalData.topology
    tensorContraction ell ((succBlockShape m h).blockTensor σ L v) =
      (∏ i, (inverseStandardCharacter ψ (m i) ⟨L i, hL i⟩ : ℂ)) * tensorContraction ell v := by
  let := F.canonicalTopologicalData.topology
  induction v using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    rw [map_smul, map_smul, map_smul, BlockShape.blockTensor_tprod, tensorContraction_tprod,
      tensorContraction_tprod, smul_eq_mul, smul_eq_mul, mul_left_comm, ← Finset.prod_mul_distrib]
    congr 2
    funext i
    exact hell i ⟨L i, hL i⟩ (v i)
  | add v v' hv hv' =>
    rw [map_add, map_add, hv, hv', map_add, mul_add]

/-- The inverse standard character of `n` is the product of the block characters of its
diagonal blocks and the inverse character of its corner entry `β_(m 0, 0)`. -/
theorem inverseStandardCharacter_eq_prod (n : upperUnipotent (t + 1) F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    (inverseStandardCharacter ψ t n : ℂ) =
      (∏ i, (inverseStandardCharacter ψ (m i)
        ⟨unipotentLevi h n i, unipotentLevi_mem h n i⟩ : ℂ)) *
        (ψ.complex (unipotentCorner h n (Fin.last (m 0)) 0))⁻¹ := by
  let := F.canonicalTopologicalData.topology
  rw [Fin.prod_univ_two, inverseStandardCharacter_apply, inverseStandardCharacter_apply,
    inverseStandardCharacter_apply, sum_superdiagonal_index h, AddChar.map_add_eq_mul,
    AddChar.map_add_eq_mul]
  change ((ψ.complex (∑ k : Fin (m 0), unipotentLevi h n 0 k.castSucc k.succ) *
      ψ.complex (unipotentCorner h n (Fin.last (m 0)) 0)) *
      ψ.complex (∑ k : Fin (m 1), unipotentLevi h n 1 k.castSucc k.succ))⁻¹ = _
  rw [mul_inv, mul_inv]
  ring

section Jacquet

variable [MeasurableSpace F.Carrier] [MeasurableAdd₂ F.Carrier] [MeasurableMul F.Carrier]

/-- The coordinate change `x ↦ n_0⁻¹ (β + x n_1)` preserves every Borel additive Haar
measure on the upper radical. -/
theorem integral_comp_unipotentShift :
    letI := F.canonicalTopologicalData.topology
    ∀ [BorelSpace (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier)]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier)) [μ.IsAddHaarMeasure]
      (n : upperUnipotent (t + 1) F.Carrier)
      (G : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier → ℂ),
      ∫ x, G (unipotentShift h n x) ∂μ = ∫ x, G x ∂μ := by
  let := F.canonicalTopologicalData.topology
  intro _ μ _ n G
  have : MeasurableAdd (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier) :=
    inferInstanceAs (MeasurableAdd (Fin (m 0 + 1) → Fin (m 1 + 1) → F.Carrier))
  let e := Shahidi.rectangularConj (unipotentLevi h n 0) (unipotentLevi h n 1)
  let c : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier :=
    ((unipotentLevi h n 0)⁻¹ : GeneralLinear (m 0 + 1) F.Carrier).val * unipotentCorner h n
  have hμ : μ.map e = μ := by
    simpa only [determinantNorm_eq_one_of_mem_upperUnipotent F _ (unipotentLevi_mem h n 0),
      determinantNorm_eq_one_of_mem_upperUnipotent F _ (unipotentLevi_mem h n 1),
      Units.val_one, one_pow, div_one, one_smul] using
      Shahidi.map_rectangularConj_padic F F.canonicalTopologicalData μ (unipotentLevi h n 0)
        (unipotentLevi h n 1)
  have hshift : ∀ x, unipotentShift h n x = c + e x := by
    intro x
    rw [unipotentShift, Shahidi.rectangularConj_apply, Matrix.mul_add, Matrix.mul_assoc]
  simp_rw [hshift]
  calc ∫ x, G (c + e x) ∂μ = ∫ y, G (c + y) ∂(μ.map e) :=
        (integral_map_equiv e (fun y => G (c + y))).symm
    _ = ∫ y, G (c + y) ∂μ := by rw [hμ]
    _ = ∫ y, G y ∂μ := integral_add_left_eq_self G c

variable (ell : ∀ i, W i →ₗ[ℂ] ℂ)

/-- JPSS (4.6.2) at the identity is `ψ⁻¹`-equivariant under upper unipotent translation,
for every section: `J(ρ(n) f)(1) = ψ⁻¹(n) J(f)(1)`. This is a change of variables and
needs no integrability. -/
theorem jacquetFunction_inducedRep_upperUnipotent
    (hell : ∀ i, letI := F.canonicalTopologicalData.topology
      ell i ∈ glInverseFunctionals ψ (m i) (σ i)) :
    letI := F.canonicalTopologicalData.topology
    ∀ [BorelSpace (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier)]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier)) [μ.IsAddHaarMeasure]
      (n : upperUnipotent (t + 1) F.Carrier) (f : Sections F h σ),
      jacquetFunction ψ ell μ (inducedRep F h σ n f) 1 =
        (inverseStandardCharacter ψ t n : ℂ) * jacquetFunction ψ ell μ f 1 := by
  let := F.canonicalTopologicalData.topology
  intro _ μ _ n f
  let G : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier → ℂ := fun y =>
    tensorContraction ell (sectionEval F h σ f (upperRadical h F.Carrier y * 1)) *
      ψ.complex (y (Fin.last (m 0)) 0)
  have hne : ψ.complex (unipotentCorner h n (Fin.last (m 0)) 0) ≠ 0 := by
    intro h0
    have h1 := ψ.norm_complex (unipotentCorner h n (Fin.last (m 0)) 0)
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have hpt : ∀ x,
      tensorContraction ell (sectionEval F h σ (inducedRep F h σ n f)
        (upperRadical h F.Carrier x * 1)) * ψ.complex (x (Fin.last (m 0)) 0) =
        (inverseStandardCharacter ψ t n : ℂ) * G (unipotentShift h n x) := by
    intro x
    simp only [G, mul_one]
    change tensorContraction ell (radicalRestriction F h σ (inducedRep F h σ n f) x) * _ =
      _ * (tensorContraction ell (radicalRestriction F h σ f (unipotentShift h n x)) * _)
    rw [radicalRestriction_inducedRep, tensorContraction_blockTensor F h σ ψ ell hell _
      (unipotentLevi_mem h n), unipotentShift_last_zero, AddChar.map_add_eq_mul,
      inverseStandardCharacter_eq_prod F h ψ n]
    field_simp
  rw [jacquetFunction_apply, jacquetFunction_apply,
    integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    integral_comp_unipotentShift F h μ n G]

omit [MeasurableAdd₂ F.Carrier] [MeasurableMul F.Carrier] in
/-- Sections with compact radical restriction have absolutely integrable JPSS integrand at
the identity, for every locally finite measure. -/
theorem isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule :
    letI := F.canonicalTopologicalData.topology
    ∀ [OpensMeasurableSpace (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier)]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))
      [IsFiniteMeasureOnCompacts μ] {f : Sections F h σ},
      f ∈ compactRadicalSubmodule F h σ → IsAbsIntegrableAt ψ ell μ f 1 := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro _ μ _ f hf
  have hc : Continuous (fun x => tensorContraction ell (radicalRestriction F h σ f x)) :=
    (((Induction.eval_isLocallyConstant _ _ f).comp (tensorContraction ell)).comp_continuous
      (continuous_upperRadical h F.Carrier)).continuous
  have hs : HasCompactSupport (fun x => tensorContraction ell (radicalRestriction F h σ f x)) :=
    hf.comp_left (map_zero _)
  have hfun : integrand ψ ell f 1 =
      fun x => tensorContraction ell (radicalRestriction F h σ f x) * positiveKernel ψ x := by
    funext x
    rw [integrand_def, scalarSection_one, mul_one]
    rfl
  unfold IsAbsIntegrableAt
  rw [hfun]
  exact (hc.mul (continuous_positiveKernel ψ)).integrable_of_hasCompactSupport hs.mul_right

/-- JPSS (4.6.2) at the identity, as a linear functional on the compact-radical
sections, given integrability there. -/
def compactRadicalJacquet (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))
    (hint : ∀ f ∈ compactRadicalSubmodule F h σ, IsAbsIntegrableAt ψ ell μ f 1) :
    compactRadicalSubmodule F h σ →ₗ[ℂ] ℂ where
  toFun f := jacquetFunction ψ ell μ f.val 1
  map_add' f f' := jacquetFunction_add ψ ell μ (hint f f.property) (hint f' f'.property)
  map_smul' c f := jacquetFunction_smul ψ ell μ c f.val 1

omit [MeasurableAdd₂ F.Carrier] [MeasurableMul F.Carrier] in
theorem compactRadicalJacquet_apply
    (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))
    (hint : ∀ f ∈ compactRadicalSubmodule F h σ, IsAbsIntegrableAt ψ ell μ f 1)
    (f : compactRadicalSubmodule F h σ) :
    compactRadicalJacquet F h σ ψ ell μ hint f = jacquetFunction ψ ell μ f.val 1 :=
  rfl

/-- The compact-radical functional is `ψ⁻¹`-equivariant under the upper unipotent group. -/
theorem compactRadicalJacquet_inducedRep
    (hell : ∀ i, letI := F.canonicalTopologicalData.topology
      ell i ∈ glInverseFunctionals ψ (m i) (σ i)) :
    letI := F.canonicalTopologicalData.topology
    ∀ [BorelSpace (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier)]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier)) [μ.IsAddHaarMeasure]
      (hint : ∀ f ∈ compactRadicalSubmodule F h σ, IsAbsIntegrableAt ψ ell μ f 1)
      (n : upperUnipotent (t + 1) F.Carrier) (f : compactRadicalSubmodule F h σ),
      compactRadicalJacquet F h σ ψ ell μ hint
          ⟨inducedRep F h σ n f, inducedRep_mem_compactRadicalSubmodule F h σ n f.property⟩ =
        (inverseStandardCharacter ψ t n : ℂ) * compactRadicalJacquet F h σ ψ ell μ hint f := by
  let := F.canonicalTopologicalData.topology
  intro _ μ _ hint n f
  exact jacquetFunction_inducedRep_upperUnipotent F h σ ψ ell hell μ n f.val

end Jacquet

end Contraction

end Sections

end Langlands.RankinSelberg.TwoBlockDeformation
