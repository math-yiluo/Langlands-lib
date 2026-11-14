import Langlands.Representation.Conductor.SphericalCyclicity.Blocks
import Langlands.Representation.Conductor.UnramifiedPrincipalSeries
import Langlands.Representation.Unramified.MinusculeCosets
import Langlands.Representation.Conductor.PrincipalCongruenceBasisProof
import Langlands.Representation.Conductor.JacquetScaledLevel

/-!
# The big cell of the `(1, n + 1)` block decomposition

For `x ∈ GL_(n+2)(F)` with lower-right block `D` and first-column tail `c` we say
that `x` lies in the cell when `D` is invertible and every coordinate of `D⁻¹ c` has
valuation below one.  This file proves that left multiplication by a matrix with
vanishing first-column tail preserves the cell and the vector `D⁻¹ c` and multiplies
the lower-right block, and records the block form of `t' = diag(1, ϖ, …, ϖ)` and of
its conjugation action.  Right multiplication by the parahoric subgroup is treated in
`SphericalCyclicity.Parahoric`.
-/

noncomputable section

namespace Langlands.Conductor.SphericalCyclicity

open Matrix Langlands.GeneralLinear Langlands.Conductor
open Langlands.Conductor.UnramifiedPrincipalSeries
open scoped BigOperators

universe uF

variable {F : Type uF} [Field F] [ValuativeRel F]

set_option quotPrecheck false in
local notation "𝒱" => ValuativeRel.valuation F
set_option quotPrecheck false in
local notation "𝒪" => (ValuativeRel.valuation F).integer

/-! ### Valuation helpers -/

theorem val_le_one_of_mem {x : F} (hx : x ∈ 𝒪) : 𝒱 x ≤ 1 :=
  (Valuation.mem_integer_iff _ _).1 hx

theorem mem_of_val_le_one {x : F} (hx : 𝒱 x ≤ 1) : x ∈ 𝒪 :=
  (Valuation.mem_integer_iff _ _).2 hx

theorem val_mul_lt_one {x y : F} (hx : 𝒱 x ≤ 1) (hy : 𝒱 y < 1) : 𝒱 (x * y) < 1 := by
  rw [map_mul]
  exact Right.mul_lt_one_of_le_of_lt hx hy

theorem val_eq_one_of_mul_eq_one {a b : F} (ha : 𝒱 a ≤ 1) (hb : 𝒱 b ≤ 1)
    (h : 𝒱 (a * b) = 1) : 𝒱 a = 1 ∧ 𝒱 b = 1 := by
  rw [map_mul] at h
  constructor
  · by_contra hne
    have := mul_lt_one_of_lt_of_le (lt_of_le_of_ne ha hne) hb
    rw [h] at this
    exact lt_irrefl _ this
  · by_contra hne
    have := Right.mul_lt_one_of_le_of_lt ha (lt_of_le_of_ne hb hne)
    rw [h] at this
    exact lt_irrefl _ this

/-- An integral matrix maps vectors with coordinates in the maximal ideal to such vectors. -/
theorem mulVec_val_lt_one {m : ℕ} {A : Matrix (Fin m) (Fin m) F} (hA : ∀ i j, A i j ∈ 𝒪)
    {y : Fin m → F} (hy : ∀ i, 𝒱 (y i) < 1) (i : Fin m) : 𝒱 ((A *ᵥ y) i) < 1 := by
  simp only [mulVec, dotProduct]
  exact Valuation.map_sum_lt _ one_ne_zero fun j _ =>
    val_mul_lt_one (val_le_one_of_mem (hA i j)) (hy j)

/-- An integral matrix maps integral vectors to integral vectors. -/
theorem mulVec_mem {m : ℕ} {A : Matrix (Fin m) (Fin m) F} (hA : ∀ i j, A i j ∈ 𝒪)
    {y : Fin m → F} (hy : ∀ i, y i ∈ 𝒪) (i : Fin m) : (A *ᵥ y) i ∈ 𝒪 := by
  simp only [mulVec, dotProduct]
  exact sum_mem fun j _ => mul_mem (hA i j) (hy j)

theorem integral_entry {m : ℕ} {k : GL (Fin (m + 1)) F}
    (hk : k ∈ integralSubgroup 𝒪 m) (i j : Fin (m + 1)) : k i j ∈ 𝒪 :=
  ((mem_integralSubgroup 𝒪 m k).1 hk).1 i j

theorem integral_inv_entry {m : ℕ} {k : GL (Fin (m + 1)) F}
    (hk : k ∈ integralSubgroup 𝒪 m) (i j : Fin (m + 1)) : k⁻¹ i j ∈ 𝒪 :=
  ((mem_integralSubgroup 𝒪 m k).1 hk).2 i j

/-! ### Determinant orders -/

variable {ϖ : Fˣ} (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ)

/-- The order of the determinant of an invertible matrix. -/
def ordDet {m : ℕ} (g : GL (Fin m) F) : ℤ :=
  ord hϖ (Matrix.GeneralLinearGroup.det g)

theorem ordDet_mul {m : ℕ} (g h : GL (Fin m) F) :
    ordDet hϖ (g * h) = ordDet hϖ g + ordDet hϖ h := by
  simp [ordDet]

@[simp] theorem ordDet_one {m : ℕ} : ordDet hϖ (1 : GL (Fin m) F) = 0 := by
  simp [ordDet]

theorem ordDet_eq_zero_of_integral {m : ℕ} {k : GL (Fin (m + 1)) F}
    (hk : k ∈ integralSubgroup 𝒪 m) : ordDet hϖ k = 0 := by
  rw [ordDet, ord_eq_zero_iff]
  exact Unramified.MinusculeCosets.valuation_det_eq_one hk

/-! ### The lower-right block as an invertible matrix -/

variable {n : ℕ}

open Classical in
/-- The lower-right block of `x`, as an invertible matrix when it is invertible
(and `1` otherwise). -/
def lowGL (x : GL (Fin (n + 2)) F) : GL (Fin (n + 1)) F :=
  if h : IsUnit (low x.val).det then Matrix.GeneralLinearGroup.mk'' (low x.val) h else 1

omit [ValuativeRel F] in
theorem lowGL_val {x : GL (Fin (n + 2)) F} (h : IsUnit (low x.val).det) :
    (lowGL x).val = low x.val := by
  rw [lowGL, dite_cond_eq_true (eq_true h)]
  rfl

/-- The vector `D⁻¹ c`, for the lower-right block `D` and first-column tail `c`. -/
def cellVec (x : GL (Fin (n + 2)) F) : Fin (n + 1) → F :=
  (low x.val)⁻¹ *ᵥ colT x.val

/-- The big cell: the lower-right block is invertible and `D⁻¹ c` has all
coordinates in the maximal ideal. -/
def InCell (x : GL (Fin (n + 2)) F) : Prop :=
  IsUnit (low x.val).det ∧ ∀ i, 𝒱 (cellVec x i) < 1

omit [ValuativeRel F] in
theorem low_mul_of_colT_eq_zero {m : ℕ} {X : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hX : colT X = 0) (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) F) :
    low (X * Y) = low X * low Y := by
  rw [low_mul, hX]
  simp

omit [ValuativeRel F] in
theorem colT_mul_of_colT_eq_zero {m : ℕ} {X : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hX : colT X = 0) (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) F) :
    colT (X * Y) = low X *ᵥ colT Y := by
  rw [colT_mul, hX]
  simp

omit [ValuativeRel F] in
theorem det_eq_of_colT_eq_zero {p : GL (Fin (n + 2)) F} (hp : colT p.val = 0) :
    p.val.det = p.val 0 0 * (low p.val).det :=
  det_of_colT_eq_zero _ hp

omit [ValuativeRel F] in
theorem isUnit_of_colT_eq_zero {p : GL (Fin (n + 2)) F} (hp : colT p.val = 0) :
    IsUnit (low p.val).det ∧ p.val 0 0 ≠ 0 := by
  have hdet : p.val.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det _).1 p.isUnit |>.ne_zero
  rw [det_eq_of_colT_eq_zero hp] at hdet
  exact ⟨isUnit_iff_ne_zero.2 (right_ne_zero_of_mul hdet), left_ne_zero_of_mul hdet⟩

theorem cellVec_mul_of_colT_eq_zero {p : GL (Fin (n + 2)) F} (hp : colT p.val = 0)
    (x : GL (Fin (n + 2)) F) : cellVec (p * x) = cellVec x := by
  have hu := (isUnit_of_colT_eq_zero hp).1
  simp only [cellVec, Units.val_mul, low_mul_of_colT_eq_zero hp, colT_mul_of_colT_eq_zero hp,
    Matrix.mul_inv_rev, mulVec_mulVec, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

theorem isUnit_det_low_mul_iff {p : GL (Fin (n + 2)) F} (hp : colT p.val = 0)
    (x : GL (Fin (n + 2)) F) : IsUnit (low (p * x).val).det ↔ IsUnit (low x.val).det := by
  have hu := (isUnit_of_colT_eq_zero hp).1
  rw [Units.val_mul, low_mul_of_colT_eq_zero hp, det_mul, IsUnit.mul_iff]
  exact ⟨fun h => h.2, fun h => ⟨hu, h⟩⟩

theorem inCell_mul_iff {p : GL (Fin (n + 2)) F} (hp : colT p.val = 0)
    (x : GL (Fin (n + 2)) F) : InCell (p * x) ↔ InCell x := by
  rw [InCell, InCell, isUnit_det_low_mul_iff hp, cellVec_mul_of_colT_eq_zero hp]

theorem lowGL_mul_of_colT_eq_zero {p : GL (Fin (n + 2)) F} (hp : colT p.val = 0)
    {x : GL (Fin (n + 2)) F} (hx : IsUnit (low x.val).det) :
    lowGL (p * x) = lowGL p * lowGL x := by
  apply Units.ext
  rw [lowGL_val ((isUnit_det_low_mul_iff hp x).2 hx), Units.val_mul, Units.val_mul,
    lowGL_val (isUnit_of_colT_eq_zero hp).1, lowGL_val hx, low_mul_of_colT_eq_zero hp]

/-- The head entry of a matrix with vanishing first-column tail, as a unit. -/
def headUnit {p : GL (Fin (n + 2)) F} (hp : colT p.val = 0) : Fˣ :=
  Units.mk0 (p.val 0 0) (isUnit_of_colT_eq_zero hp).2

theorem ordDet_of_colT_eq_zero {p : GL (Fin (n + 2)) F} (hp : colT p.val = 0) :
    ordDet hϖ p = ord hϖ (headUnit hp) + ordDet hϖ (lowGL p) := by
  have h : Matrix.GeneralLinearGroup.det p =
      headUnit hp * Matrix.GeneralLinearGroup.det (lowGL p) := by
    apply Units.ext
    rw [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.GeneralLinearGroup.val_det_apply, lowGL_val (isUnit_of_colT_eq_zero hp).1,
      det_eq_of_colT_eq_zero hp]
    rfl
  rw [ordDet, h, ord_mul]
  rfl

/-! ### Explicit elements -/

omit [ValuativeRel F] in
theorem colT_lowerUnip {m : ℕ} (y : Fin m → F) : colT (lowerUnip y).val = y := rfl

omit [ValuativeRel F] in
theorem low_lowerUnip {m : ℕ} (y : Fin m → F) : low (lowerUnip y).val = 1 := rfl

omit [ValuativeRel F] in
theorem colT_blockDiag {m : ℕ} (α : Fˣ) (h : GL (Fin m) F) :
    colT (blockDiag α h).val = 0 := rfl

omit [ValuativeRel F] in
theorem low_blockDiag {m : ℕ} (α : Fˣ) (h : GL (Fin m) F) :
    low (blockDiag α h).val = h.val := rfl

omit [ValuativeRel F] in
theorem blockDiag_inv {m : ℕ} (α : Fˣ) (h : GL (Fin m) F) :
    (blockDiag α h)⁻¹ = blockDiag α⁻¹ h⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, blockDiag_mul, mul_inv_cancel, mul_inv_cancel]
  apply Units.ext
  rw [blockDiag_val, Units.val_one, Units.val_one, Units.val_one, blk_one]

/-- The element `diag(1, ϖ, …, ϖ)`. -/
def tPrime (ϖ : Fˣ) : GL (Fin (n + 2)) F :=
  blockDiag 1 (Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) ϖ)

omit [ValuativeRel F] in
theorem tPrime_conj_val (x : GL (Fin (n + 2)) F) :
    ((tPrime ϖ)⁻¹ * x * tPrime ϖ).val =
      blk (x.val 0 0) ((ϖ : F) • rowT x.val) ((ϖ : F)⁻¹ • colT x.val) (low x.val) := by
  rw [tPrime, blockDiag_inv]
  conv_lhs => rw [Units.val_mul, Units.val_mul, blockDiag_val, blockDiag_val, ← blk_eta x.val]
  rw [blk_mul, blk_mul]
  have hs : ((Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) ϖ : GL (Fin (n + 1)) F) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) F) = (ϖ : F) • 1 := by
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, smul_one_eq_diagonal]
  have hs' : (((Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) ϖ)⁻¹ : GL (Fin (n + 1)) F) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) F) = (ϖ : F)⁻¹ • 1 := by
    rw [← map_inv, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      smul_one_eq_diagonal, Units.val_inv_eq_inv_val]
  rw [hs, hs']
  congr 1
  · simp
  · ext j; simp [vecMul, dotProduct, Matrix.one_apply, mul_comm]
  · ext i; simp [mulVec, dotProduct, Matrix.one_apply]
  · ext i j; simp

theorem tPrime_inv_lowerUnip_tPrime (y : Fin (n + 1) → F) :
    (tPrime ϖ)⁻¹ * lowerUnip y * tPrime ϖ = lowerUnip ((ϖ : F)⁻¹ • y) := by
  apply Units.ext
  rw [tPrime_conj_val, lowerUnip_val]
  simp

end Langlands.Conductor.SphericalCyclicity
