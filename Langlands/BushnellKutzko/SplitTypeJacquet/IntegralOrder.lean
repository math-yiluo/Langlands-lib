import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! # Block-triangular integrality conditions and their unit groups

For a block function `blk : ι → ℕ` on a finite index type, `InOrd blk x` says that the matrix
`x` over a field with a valuative relation is integral and that its entries below the block
diagonal lie in the maximal ideal; `InRad blk x` puts the block diagonal entries in the maximal
ideal as well. The invertible matrices `g` with `InOrd g` and `InOrd g⁻¹` form `J0 blk`, and
`J1 blk` is the subgroup of those with `InRad (g - 1)`. Over a nonarchimedean local field, in
coordinates adapted to a lattice chain, these describe a hereditary order, its radical and the
groups `U(𝔄)`, `U^1(𝔄)` (module `LayerCoordinates`). -/

open ValuativeRel Matrix

noncomputable section

namespace Langlands.BushnellKutzko.SplitTypeJacquet

universe uF

variable {F : Type uF} [Field F] [ValuativeRel F] {ι : Type*}

section Uniformizer

variable {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
include hϖ

theorem uniformizer_ne_zero' : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)

theorem val_uniformizer_lt_one : valuation F (ϖ : F) < 1 :=
  (valuation F).mem_maximalIdeal_iff.mp
    ((IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit)

theorem val_uniformizer_mul_lt_one {x : F} (hx : valuation F x ≤ 1) :
    valuation F ((ϖ : F) * x) < 1 := by
  rw [map_mul]
  calc valuation F (ϖ : F) * valuation F x ≤ valuation F (ϖ : F) * 1 := mul_le_mul' le_rfl hx
    _ < 1 := by rw [mul_one]; exact val_uniformizer_lt_one hϖ

end Uniformizer

/-- Integral entries, with the entries strictly below the block diagonal in the maximal
ideal. -/
def InOrd (blk : ι → ℕ) (x : Matrix ι ι F) : Prop :=
  ∀ p q : ι, valuation F (x p q) ≤ 1 ∧ (blk q < blk p → valuation F (x p q) < 1)

/-- Integral entries, with the entries on and below the block diagonal in the maximal ideal. -/
def InRad (blk : ι → ℕ) (x : Matrix ι ι F) : Prop :=
  ∀ p q : ι, valuation F (x p q) ≤ 1 ∧ (blk q ≤ blk p → valuation F (x p q) < 1)

variable {blk : ι → ℕ}

theorem InRad.inOrd {x : Matrix ι ι F} (h : InRad blk x) : InOrd blk x :=
  fun p q => ⟨(h p q).1, fun hpq => (h p q).2 hpq.le⟩

theorem inOrd_one [DecidableEq ι] : InOrd blk (1 : Matrix ι ι F) := by
  intro p q
  by_cases hpq : p = q
  · subst hpq
    simp
  · simp [Matrix.one_apply_ne hpq]

theorem inRad_zero : InRad blk (0 : Matrix ι ι F) := by
  intro p q
  simp

private theorem val_mul_lt_one_left {a b : F} (ha : valuation F a < 1) (hb : valuation F b ≤ 1) :
    valuation F (a * b) < 1 := by
  rw [map_mul]
  calc valuation F a * valuation F b ≤ valuation F a * 1 := mul_le_mul' le_rfl hb
    _ < 1 := by rwa [mul_one]

private theorem val_mul_lt_one_right {a b : F} (ha : valuation F a ≤ 1) (hb : valuation F b < 1) :
    valuation F (a * b) < 1 := by
  rw [mul_comm]
  exact val_mul_lt_one_left hb ha

private theorem val_mul_le_one {a b : F} (ha : valuation F a ≤ 1) (hb : valuation F b ≤ 1) :
    valuation F (a * b) ≤ 1 := by
  rw [map_mul]
  exact mul_le_one' ha hb

theorem InOrd.add {x y : Matrix ι ι F} (hx : InOrd blk x) (hy : InOrd blk y) :
    InOrd blk (x + y) := fun p q =>
  ⟨Valuation.map_add_le _ (hx p q).1 (hy p q).1,
    fun h => Valuation.map_add_lt _ ((hx p q).2 h) ((hy p q).2 h)⟩

theorem InRad.add {x y : Matrix ι ι F} (hx : InRad blk x) (hy : InRad blk y) :
    InRad blk (x + y) := fun p q =>
  ⟨Valuation.map_add_le _ (hx p q).1 (hy p q).1,
    fun h => Valuation.map_add_lt _ ((hx p q).2 h) ((hy p q).2 h)⟩

theorem InRad.neg {x : Matrix ι ι F} (hx : InRad blk x) : InRad blk (-x) := fun p q => by
  simpa [Valuation.map_neg] using hx p q

theorem InOrd.neg {x : Matrix ι ι F} (hx : InOrd blk x) : InOrd blk (-x) := fun p q => by
  simpa [Valuation.map_neg] using hx p q

variable [Fintype ι]

theorem InOrd.mul {x y : Matrix ι ι F} (hx : InOrd blk x) (hy : InOrd blk y) :
    InOrd blk (x * y) := by
  intro p q
  refine ⟨?_, fun hpq => ?_⟩
  · rw [Matrix.mul_apply]
    exact Valuation.map_sum_le _ fun r _ => val_mul_le_one (hx p r).1 (hy r q).1
  · rw [Matrix.mul_apply]
    refine Valuation.map_sum_lt _ one_ne_zero fun r _ => ?_
    by_cases hr : blk r < blk p
    · exact val_mul_lt_one_left ((hx p r).2 hr) (hy r q).1
    · exact val_mul_lt_one_right (hx p r).1 ((hy r q).2 (lt_of_lt_of_le hpq (not_lt.mp hr)))

theorem InOrd.mul_inRad {x y : Matrix ι ι F} (hx : InOrd blk x) (hy : InRad blk y) :
    InRad blk (x * y) := by
  intro p q
  refine ⟨?_, fun hpq => ?_⟩
  · rw [Matrix.mul_apply]
    exact Valuation.map_sum_le _ fun r _ => val_mul_le_one (hx p r).1 (hy r q).1
  · rw [Matrix.mul_apply]
    refine Valuation.map_sum_lt _ one_ne_zero fun r _ => ?_
    by_cases hr : blk r < blk p
    · exact val_mul_lt_one_left ((hx p r).2 hr) (hy r q).1
    · exact val_mul_lt_one_right (hx p r).1 ((hy r q).2 (le_trans hpq (not_lt.mp hr)))

theorem InRad.mul_inOrd {x y : Matrix ι ι F} (hx : InRad blk x) (hy : InOrd blk y) :
    InRad blk (x * y) := by
  intro p q
  refine ⟨?_, fun hpq => ?_⟩
  · rw [Matrix.mul_apply]
    exact Valuation.map_sum_le _ fun r _ => val_mul_le_one (hx p r).1 (hy r q).1
  · rw [Matrix.mul_apply]
    refine Valuation.map_sum_lt _ one_ne_zero fun r _ => ?_
    by_cases hr : blk r ≤ blk p
    · exact val_mul_lt_one_left ((hx p r).2 hr) (hy r q).1
    · exact val_mul_lt_one_right (hx p r).1 ((hy r q).2 (lt_of_le_of_lt hpq (not_le.mp hr)))

variable [DecidableEq ι]

variable (F) in
/-- The invertible matrices `g` with `InOrd g` and `InOrd g⁻¹`. Over a nonarchimedean local
field, in coordinates adapted to a lattice chain, this is the unit group `U(𝔄)` of its hereditary
order. -/
def J0 (blk : ι → ℕ) : Subgroup (GL ι F) where
  carrier := {g | InOrd blk (g : Matrix ι ι F) ∧ InOrd blk ((g⁻¹ : GL ι F) : Matrix ι ι F)}
  one_mem' := ⟨by simpa using inOrd_one, by simpa using inOrd_one⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨by simpa using ha.mul hb, by simpa [_root_.mul_inv_rev] using hb'.mul ha'⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨ha', by simpa using ha⟩

variable (F) in
/-- The elements `g` of `J0 blk` with `InRad (g - 1)`. Over a nonarchimedean local field, in
coordinates adapted to a lattice chain, this is the group `U^1(𝔄)`. -/
def J1 (blk : ι → ℕ) : Subgroup (GL ι F) where
  carrier := {g | g ∈ J0 F blk ∧ InRad blk ((g : Matrix ι ι F) - 1)}
  one_mem' := ⟨(J0 F blk).one_mem, by simpa using inRad_zero⟩
  mul_mem' := by
    rintro a b ⟨ha, ha1⟩ ⟨hb, hb1⟩
    refine ⟨(J0 F blk).mul_mem ha hb, ?_⟩
    have h : ((a * b : GL ι F) : Matrix ι ι F) - 1 =
        (a : Matrix ι ι F) * ((b : Matrix ι ι F) - 1) + ((a : Matrix ι ι F) - 1) := by
      simp only [Units.val_mul]
      noncomm_ring
    rw [h]
    exact (ha.1.mul_inRad hb1).add ha1
  inv_mem' := by
    rintro a ⟨ha, ha1⟩
    refine ⟨(J0 F blk).inv_mem ha, ?_⟩
    have h : ((a⁻¹ : GL ι F) : Matrix ι ι F) - 1 =
        -(((a⁻¹ : GL ι F) : Matrix ι ι F) * ((a : Matrix ι ι F) - 1)) := by
      rw [mul_sub, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
      noncomm_ring
    rw [h]
    exact (ha.2.mul_inRad ha1).neg

theorem J1_le_J0 : J1 F blk ≤ J0 F blk := fun _ h => h.1

omit [Fintype ι] in
theorem inOrd_of_inRad_sub_one {x : Matrix ι ι F} (h : InRad blk (x - 1)) : InOrd blk x := by
  simpa using h.inOrd.add inOrd_one

theorem mem_J1_of_inRad {g : GL ι F} (h : InRad blk ((g : Matrix ι ι F) - 1))
    (h' : InRad blk (((g⁻¹ : GL ι F) : Matrix ι ι F) - 1)) : g ∈ J1 F blk :=
  ⟨⟨inOrd_of_inRad_sub_one h, inOrd_of_inRad_sub_one h'⟩, h⟩

/-- `J1 blk` is normal in `J0 blk`. -/
theorem conj_mem_J1 {g x : GL ι F} (hg : g ∈ J0 F blk) (hx : x ∈ J1 F blk) :
    g * x * g⁻¹ ∈ J1 F blk := by
  refine ⟨(J0 F blk).mul_mem ((J0 F blk).mul_mem hg hx.1) ((J0 F blk).inv_mem hg), ?_⟩
  have h : ((g * x * g⁻¹ : GL ι F) : Matrix ι ι F) - 1 =
      (g : Matrix ι ι F) * ((x : Matrix ι ι F) - 1) * ((g⁻¹ : GL ι F) : Matrix ι ι F) := by
    have hGG : (g : Matrix ι ι F) * ((g⁻¹ : GL ι F) : Matrix ι ι F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, hGG]
  rw [h]
  exact (hg.1.mul_inRad hx.2).mul_inOrd hg.2

/-- Products of integral matrices are integral. -/
theorem int_mul_le_one {κ μ ν : Type*} [Fintype μ] {A : Matrix κ μ F} {B : Matrix μ ν F}
    (hA : ∀ i j, valuation F (A i j) ≤ 1) (hB : ∀ i j, valuation F (B i j) ≤ 1) (i : κ) (j : ν) :
    valuation F ((A * B) i j) ≤ 1 := by
  rw [Matrix.mul_apply]
  exact Valuation.map_sum_le _ fun c _ => val_mul_le_one (hA i c) (hB c j)

/-- An integral matrix times a matrix with entries in the maximal ideal has entries in the
maximal ideal. -/
theorem int_mul_lt_one {κ μ ν : Type*} [Fintype μ] {A : Matrix κ μ F} {B : Matrix μ ν F}
    (hA : ∀ i j, valuation F (A i j) ≤ 1) (hB : ∀ i j, valuation F (B i j) < 1) (i : κ) (j : ν) :
    valuation F ((A * B) i j) < 1 := by
  rw [Matrix.mul_apply]
  exact Valuation.map_sum_lt _ one_ne_zero fun c _ => val_mul_lt_one_right (hA i c) (hB c j)

/-- A matrix with entries in the maximal ideal times an integral matrix has entries in the
maximal ideal. -/
theorem lt_one_mul_int {κ μ ν : Type*} [Fintype μ] {A : Matrix κ μ F} {B : Matrix μ ν F}
    (hA : ∀ i j, valuation F (A i j) < 1) (hB : ∀ i j, valuation F (B i j) ≤ 1) (i : κ) (j : ν) :
    valuation F ((A * B) i j) < 1 := by
  rw [Matrix.mul_apply]
  exact Valuation.map_sum_lt _ one_ne_zero fun c _ => val_mul_lt_one_left (hA i c) (hB c j)

/-- A matrix congruent to the identity modulo the maximal ideal is invertible with integral
inverse. -/
theorem exists_intGL_of_sub_one {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ F) (h : ∀ p q, valuation F (A p q - (1 : Matrix κ κ F) p q) < 1) :
    ∃ Ag : GL κ F, (Ag : Matrix κ κ F) = A ∧
      ∀ p q, valuation F (((Ag⁻¹ : GL κ F) : Matrix κ κ F) p q) ≤ 1 := by
  have h1 : ∀ p q, valuation F ((1 : Matrix κ κ F) p q) ≤ 1 := by
    intro p q; by_cases hpq : p = q <;> simp [hpq, Matrix.one_apply]
  have hint : ∀ p q, valuation F (A p q) ≤ 1 := fun p q => by
    have := Valuation.map_add_le _ (h p q).le (h1 p q)
    simpa using this
  let AO : Matrix κ κ 𝒪[F] := fun p q => ⟨A p q, hint p q⟩
  let IO : Matrix κ κ 𝒪[F] := fun p q => ⟨(1 : Matrix κ κ F) p q, h1 p q⟩
  have hIO : IO = 1 := by
    ext p q
    by_cases hpq : p = q
    · subst hpq; simp [IO]
    · simp [IO, Matrix.one_apply_ne hpq]
  have hred : AO.map (IsLocalRing.residue 𝒪[F]) = 1 := by
    rw [← Matrix.map_one (IsLocalRing.residue 𝒪[F]) (map_zero _) (map_one _), ← hIO]
    ext p q
    simp only [Matrix.map_apply]
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact (valuation F).mem_maximalIdeal_iff.mpr (by simpa [AO, IO] using h p q)
  have hdet : IsUnit AO.det := by
    have : IsUnit (IsLocalRing.residue 𝒪[F] AO.det) := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hred, Matrix.det_one]
      exact isUnit_one
    exact isUnit_of_map_unit (IsLocalRing.residue 𝒪[F]) _ this
  let AOu : GL κ 𝒪[F] := ((Matrix.isUnit_iff_isUnit_det _).mpr hdet).unit
  refine ⟨Matrix.GeneralLinearGroup.map (Subring.subtype 𝒪[F]) AOu, ?_, fun p q => ?_⟩
  · ext p q; rfl
  · rw [← map_inv]
    exact (((AOu⁻¹ : GL κ 𝒪[F]) : Matrix κ κ 𝒪[F]) p q).2

end Langlands.BushnellKutzko.SplitTypeJacquet
