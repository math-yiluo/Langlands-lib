import Langlands.Global.RankinSelberg.DualExpansionRectStep

/-! # The radical `Y_(n,m)` as `𝔸^{(m+1)×K} ⋊ N_K` -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Topology
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global
open Langlands.Automorphic.CuspidalWhittaker (sqZeroUnit sqZeroUnit_val ratVec ratVec_apply)

variable {F : Type u} [Field F] [NumberField F]

local instance dualRadSchemeAffine (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance dualRadSchemeSmooth (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable {m K : ℕ}

section Matrices

variable {R : Type*} [CommRing R]

variable (m K) in
/-- The rectangular block of `Y_(m+K+1,m)`: rows `≤ m`, columns `≥ m + 1`. -/
def yMat (A : Fin (m + 1) × Fin K → R) : Matrix (Fin (m + K + 1)) (Fin (m + K + 1)) R :=
  fun a b => if h : (a : ℕ) ≤ m ∧ m + 1 ≤ (b : ℕ) then
    A (⟨a, by omega⟩, ⟨(b : ℕ) - (m + 1), by omega⟩) else 0

theorem yMat_mul_yMat (A B : Fin (m + 1) × Fin K → R) : yMat m K A * yMat m K B = 0 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  simp only [yMat]
  split_ifs with h1 h2 <;> first | simp | (exfalso; omega)

theorem yMat_add (A B : Fin (m + 1) × Fin K → R) :
    yMat m K (A + B) = yMat m K A + yMat m K B := by
  ext a b
  simp only [yMat, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

theorem yMat_zero : yMat m K (0 : Fin (m + 1) × Fin K → R) = 0 := by
  ext a b
  simp only [yMat, Pi.zero_apply, Matrix.zero_apply]
  split_ifs <;> rfl

theorem yMat_neg (A : Fin (m + 1) × Fin K → R) : yMat m K (-A) = -yMat m K A := by
  ext a b
  simp only [yMat, Pi.neg_apply, Matrix.neg_apply]
  split_ifs <;> simp

variable (m K) in
/-- The embedding `U ↦ diag(I_(m+1), U)`. -/
def brMat : Matrix (Fin K) (Fin K) R →* Matrix (Fin (m + K + 1)) (Fin (m + K + 1)) R where
  toFun A := Matrix.reindex (finCongr (by omega : m + 1 + K = m + K + 1))
    (finCongr (by omega : m + 1 + K = m + K + 1)) (lrMatrix (m + 1) K A)
  map_one' := by simp
  map_mul' A B := by
    rw [map_mul, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply,
      Matrix.submatrix_mul_equiv]

theorem brMat_apply (A : Matrix (Fin K) (Fin K) R) (a b : Fin (m + K + 1)) :
    brMat m K A a b =
      if ha : m + 1 ≤ (a : ℕ) then
        (if hb : m + 1 ≤ (b : ℕ) then A ⟨(a : ℕ) - (m + 1), by omega⟩ ⟨(b : ℕ) - (m + 1), by omega⟩
          else 0)
      else (if a = b then 1 else 0) := by
  simp only [brMat, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [lrMatrix_apply]
  simp only [finCongr_symm, finCongr_apply, Fin.val_cast, Fin.ext_iff]

variable (m K) in
/-- The embedding `U ↦ diag(I_(m+1), U)` on invertible matrices. -/
def brGL : Matrix.GeneralLinearGroup (Fin K) R →* Matrix.GeneralLinearGroup (Fin (m + K + 1)) R :=
  Units.map (brMat m K)

/-- The bottom-right `K × K` block. -/
def brSub (M : Matrix (Fin (m + K + 1)) (Fin (m + K + 1)) R) : Matrix (Fin K) (Fin K) R :=
  fun i j => M ⟨m + 1 + i, by omega⟩ ⟨m + 1 + j, by omega⟩

theorem brSub_brMat (A : Matrix (Fin K) (Fin K) R) : brSub (brMat m K A) = A := by
  ext i j
  simp only [brSub, brMat_apply]
  rw [dite_eq_left (by simp), dite_eq_left (by simp)]
  congr 1 <;> ext <;> simp

theorem brSub_one_add_yMat (A : Fin (m + 1) × Fin K → R) :
    brSub (1 + yMat m K A) = 1 := by
  ext i j
  simp only [brSub, Matrix.add_apply, yMat, Matrix.one_apply, Fin.ext_iff]
  rw [dite_eq_right (fun h => by omega)]
  simp

theorem brSub_mul {M N : Matrix (Fin (m + K + 1)) (Fin (m + K + 1)) R}
    (hM : ∀ a b : Fin (m + K + 1), (b : ℕ) ≤ m → m + 1 ≤ (a : ℕ) → M a b = 0) :
    brSub (M * N) = brSub M * brSub N := by
  ext i j
  simp only [brSub, Matrix.mul_apply]
  let e : Fin (m + 1) ⊕ Fin K ≃ Fin (m + K + 1) :=
    finSumFinEquiv.trans (finCongr (by omega))
  rw [← e.sum_comp, Fintype.sum_sum_type]
  have h0 : ∑ c : Fin (m + 1), M ⟨m + 1 + i, by omega⟩ (e (Sum.inl c)) *
      N (e (Sum.inl c)) ⟨m + 1 + j, by omega⟩ = 0 := by
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [hM _ _ (by simp [e]; omega) (by simp), zero_mul]
  rw [h0, zero_add]
  refine Finset.sum_congr rfl fun l _ => ?_
  have : e (Sum.inr l) = ⟨m + 1 + l, by omega⟩ := by ext; simp [e]
  rw [this]

end Matrices

section Points

/-- The point `1 + yMat A` of `GL_(m+K+1)(𝔸)`. -/
def yPoint (A : Fin (m + 1) × Fin K → Adeles F) : Points F (m + K + 1) :=
  (GeneralLinearGroupPoints.adelicEquiv F (m + K + 1)).symm
    (sqZeroUnit (yMat m K A) (yMat_mul_yMat A A))

theorem pointMatrix_yPoint (A : Fin (m + 1) × Fin K → Adeles F) :
    pointMatrix F (yPoint A) = 1 + yMat m K A := by
  simp only [yPoint, pointMatrix, MulEquiv.apply_symm_apply, sqZeroUnit_val]

theorem yPoint_mul (A B : Fin (m + 1) × Fin K → Adeles F) :
    yPoint A * yPoint B = yPoint (A + B) := by
  apply point_ext
  rw [pointMatrix_mul, pointMatrix_yPoint, pointMatrix_yPoint, pointMatrix_yPoint, yMat_add,
    add_mul, one_mul, mul_add, mul_one, yMat_mul_yMat, add_zero]
  abel

theorem yPoint_zero : yPoint (0 : Fin (m + 1) × Fin K → Adeles F) = 1 := by
  apply point_ext
  rw [pointMatrix_yPoint, yMat_zero, add_zero, pointMatrix_one]

/-- The point `diag(I_(m+1), u)` of `GL_(m+K+1)(𝔸)`. -/
def brPoint (u : Points F K) : Points F (m + K + 1) :=
  (GeneralLinearGroupPoints.adelicEquiv F (m + K + 1)).symm
    (brGL m K (GeneralLinearGroupPoints.adelicEquiv F K u))

theorem pointMatrix_brPoint (u : Points F K) :
    pointMatrix F (brPoint (m := m) u) = brMat m K (pointMatrix F u) := by
  simp only [brPoint, pointMatrix, MulEquiv.apply_symm_apply, brGL, Units.coe_map]

theorem brPoint_mul (u v : Points F K) :
    brPoint (m := m) (u * v) = brPoint u * brPoint v := by
  simp only [brPoint, map_mul]

theorem brPoint_one : brPoint (m := m) (1 : Points F K) = 1 := by
  simp only [brPoint, map_one]

end Points

section Membership

/-- The adelic points of `Y_(m+K+1,m)`. -/
abbrev YGroup (F : Type u) [Field F] [NumberField F] (m K : ℕ) :=
  AdelicSubgroupPoints.adelicPoints F (Scheme F (m + K + 1)) (projectionUnipotent F (m + K + 1) m)

theorem yPoint_mem (A : Fin (m + 1) × Fin K → Adeles F) :
    yPoint A ∈ YGroup F m K := by
  rw [mem_projectionAdelic_iff]
  change PrimitiveAdelicHeight.IsUnitriangular (pointMatrix F (yPoint A)) ∧
    ∀ a b : Fin (m + K + 1), (b : ℕ) ≤ m → pointMatrix F (yPoint A) a b = (1 : Matrix _ _ _) a b
  rw [pointMatrix_yPoint]
  refine ⟨⟨fun a b hab => ?_, fun a => ?_⟩, fun a b hb => ?_⟩
  · have hab' : (b : ℕ) < a := hab
    have hne : a ≠ b := fun h => by subst h; omega
    rw [Matrix.add_apply, Matrix.one_apply_ne hne]
    simp only [yMat]
    rw [dite_eq_right (fun h => by omega), add_zero]
  · simp only [Matrix.add_apply, yMat, Matrix.one_apply_eq]
    rw [dite_eq_right (fun h => by omega), add_zero]
  · simp only [Matrix.add_apply, yMat]
    rw [dite_eq_right (fun h => by omega), add_zero]

theorem brPoint_mem (u : unipotentAdelic F K) :
    brPoint (m := m) (u : Points F K) ∈ YGroup F m K := by
  have hu := isUnitriangular_of_mem_unipotentAdelic F u
  rw [mem_projectionAdelic_iff]
  change PrimitiveAdelicHeight.IsUnitriangular (pointMatrix F (brPoint (m := m) (u : Points F K))) ∧
    ∀ a b : Fin (m + K + 1), (b : ℕ) ≤ m →
      pointMatrix F (brPoint (m := m) (u : Points F K)) a b = (1 : Matrix _ _ _) a b
  rw [pointMatrix_brPoint]
  refine ⟨⟨fun a b hab => ?_, fun a => ?_⟩, fun a b hb => ?_⟩
  · have hab' : (b : ℕ) < a := hab
    rw [brMat_apply]
    split_ifs with h1 h2 h3
    · exact hu.1 (show (⟨(b : ℕ) - (m + 1), _⟩ : Fin K) < ⟨(a : ℕ) - (m + 1), _⟩ by
        simp only [Fin.mk_lt_mk]; omega)
    · rfl
    · exact absurd h3 (Fin.ne_of_gt hab)
    · rfl
  · rw [brMat_apply]
    split_ifs with h1 h2
    all_goals first | exact hu.2 _ | rfl | exact absurd rfl h2
  · rw [brMat_apply, Matrix.one_apply]
    split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)

end Membership

section Homs

theorem yGroup_lowerLeft (y : YGroup F m K) (a b : Fin (m + K + 1)) (hb : (b : ℕ) ≤ m)
    (ha : m + 1 ≤ (a : ℕ)) : pointMatrix F (y : Points F (m + K + 1)) a b = 0 := by
  have := ((mem_projectionAdelic_iff F m y.val).mp y.property).2 a b hb
  change pointMatrix F (y : Points F (m + K + 1)) a b = _ at this
  rw [this, Matrix.one_apply_ne (fun h => by subst h; omega)]

theorem isUnitriangular_yGroup (y : YGroup F m K) :
    PrimitiveAdelicHeight.IsUnitriangular (pointMatrix F (y : Points F (m + K + 1))) :=
  ((mem_projectionAdelic_iff F m y.val).mp y.property).1

theorem isUnitriangular_brSub {R : Type*} [CommRing R]
    {M : Matrix (Fin (m + K + 1)) (Fin (m + K + 1)) R}
    (hM : PrimitiveAdelicHeight.IsUnitriangular M) :
    PrimitiveAdelicHeight.IsUnitriangular (brSub (m := m) (K := K) M) :=
  ⟨fun i j hij => hM.1 (show (⟨m + 1 + j, by omega⟩ : Fin (m + K + 1)) < ⟨m + 1 + i, by omega⟩
    by simp only [Fin.mk_lt_mk]; have : (j : ℕ) < i := hij; omega), fun _ => hM.2 _⟩

variable (F m K) in
/-- The rectangle homomorphism `𝔸^{(m+1)×K} → Y(𝔸)`. -/
def yHom : ColGroup F (Fin (m + 1) × Fin K) →* YGroup F m K where
  toFun A := ⟨yPoint (Multiplicative.toAdd A), yPoint_mem _⟩
  map_one' := Subtype.ext yPoint_zero
  map_mul' A B := Subtype.ext (by
    change yPoint (Multiplicative.toAdd (A * B)) = _
    rw [toAdd_mul, ← yPoint_mul]
    rfl)

theorem coe_yHom (A : ColGroup F (Fin (m + 1) × Fin K)) :
    ((yHom F m K A : YGroup F m K) : Points F (m + K + 1)) = yPoint (Multiplicative.toAdd A) :=
  rfl

variable (F m K) in
/-- The block embedding `N_K(𝔸) → Y(𝔸)`, `u ↦ diag(I_(m+1), u)`. -/
def brHom : unipotentAdelic F K →* YGroup F m K where
  toFun u := ⟨brPoint (u : Points F K), brPoint_mem u⟩
  map_one' := Subtype.ext brPoint_one
  map_mul' _ _ := Subtype.ext (brPoint_mul _ _)

theorem coe_brHom (u : unipotentAdelic F K) :
    ((brHom F m K u : YGroup F m K) : Points F (m + K + 1)) = brPoint (u : Points F K) := rfl

/-- The bottom-right block of a point of `Y(𝔸)`. -/
def blockPoint (y : YGroup F m K) : unipotentAdelic F K :=
  ⟨(GeneralLinearGroupPoints.adelicEquiv F K).symm
      (unitriangularUnit (brSub (pointMatrix F (y : Points F (m + K + 1))))
        (isUnitriangular_brSub (isUnitriangular_yGroup y))), by
    rw [mem_unipotentAdelic_iff, MulEquiv.apply_symm_apply]
    exact isUnitriangular_brSub (isUnitriangular_yGroup y)⟩

theorem pointMatrix_blockPoint (y : YGroup F m K) :
    pointMatrix F ((blockPoint y : unipotentAdelic F K) : Points F K) =
      brSub (pointMatrix F (y : Points F (m + K + 1))) := by
  simp only [blockPoint, pointMatrix, MulEquiv.apply_symm_apply]
  rfl

variable (F m K) in
/-- The bottom-right block homomorphism `Y(𝔸) → N_K(𝔸)`. -/
def blockHom : YGroup F m K →* unipotentAdelic F K where
  toFun := blockPoint
  map_one' := Subtype.ext (by
    apply point_ext
    rw [pointMatrix_blockPoint]
    simp only [OneMemClass.coe_one, pointMatrix_one]
    ext i j
    simp only [brSub, Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega))
  map_mul' g h := Subtype.ext (by
    apply point_ext
    rw [pointMatrix_blockPoint, Subgroup.coe_mul, pointMatrix_mul,
      brSub_mul (fun a b hb ha => yGroup_lowerLeft g a b hb ha), Subgroup.coe_mul,
      pointMatrix_mul, pointMatrix_blockPoint, pointMatrix_blockPoint])

theorem blockHom_brHom (u : unipotentAdelic F K) : blockHom F m K (brHom F m K u) = u := by
  apply Subtype.ext
  apply point_ext
  change pointMatrix F ((blockPoint (brHom F m K u) : unipotentAdelic F K) : Points F K) = _
  rw [pointMatrix_blockPoint, coe_brHom, pointMatrix_brPoint, brSub_brMat]

theorem blockHom_yHom (A : ColGroup F (Fin (m + 1) × Fin K)) :
    blockHom F m K (yHom F m K A) = 1 := by
  apply Subtype.ext
  apply point_ext
  change pointMatrix F ((blockPoint (yHom F m K A) : unipotentAdelic F K) : Points F K) = _
  rw [pointMatrix_blockPoint, coe_yHom, pointMatrix_yPoint, brSub_one_add_yMat,
    OneMemClass.coe_one, pointMatrix_one]

theorem exists_yHom_eq (y : YGroup F m K) (hy : blockHom F m K y = 1) :
    ∃ A, yHom F m K A = y := by
  refine ⟨Multiplicative.ofAdd fun p => pointMatrix F (y : Points F (m + K + 1))
    ⟨p.1, by omega⟩ ⟨m + 1 + p.2, by omega⟩, ?_⟩
  have hbr : brSub (pointMatrix F (y : Points F (m + K + 1))) = 1 := by
    have := congrArg (fun x : unipotentAdelic F K => pointMatrix F (x : Points F K)) hy
    change pointMatrix F ((blockPoint y : unipotentAdelic F K) : Points F K) = _ at this
    rw [pointMatrix_blockPoint, OneMemClass.coe_one, pointMatrix_one] at this
    exact this
  have hcol := ((mem_projectionAdelic_iff F m y.val).mp y.property).2
  apply Subtype.ext
  apply point_ext
  rw [coe_yHom, pointMatrix_yPoint]
  ext a b
  simp only [Matrix.add_apply, yMat, toAdd_ofAdd]
  by_cases hb : (b : ℕ) ≤ m
  · rw [dite_eq_right (fun h => by omega), add_zero]
    exact (hcol a b hb).symm
  · by_cases ha : (a : ℕ) ≤ m
    · rw [dite_eq_left ⟨ha, by omega⟩, Matrix.one_apply_ne (fun h => by subst h; omega),
        zero_add]
      congr 1
      ext
      simp only
      omega
    · rw [dite_eq_right (fun h => by omega), add_zero]
      have := congrFun (congrFun hbr ⟨(a : ℕ) - (m + 1), by omega⟩) ⟨(b : ℕ) - (m + 1), by omega⟩
      simp only [brSub] at this
      have ea : (⟨m + 1 + ((a : ℕ) - (m + 1)), by omega⟩ : Fin (m + K + 1)) = a := by
        ext; simp only; omega
      have eb : (⟨m + 1 + ((b : ℕ) - (m + 1)), by omega⟩ : Fin (m + K + 1)) = b := by
        ext; simp only; omega
      rw [ea, eb] at this
      rw [this, Matrix.one_apply, Matrix.one_apply]
      simp only [Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega)

end Homs

section Topology

local instance dualRadYLocallyCompact :
    LocallyCompactSpace (YGroup F m K) :=
  (projectionUnipotentClosed F (m + K + 1) m).locallyCompactSpace

local instance dualRadUnipLocallyCompact (n : ℕ) : LocallyCompactSpace (unipotentAdelic F n) :=
  (isClosed_upperUnipotent_adelicPoints F n).locallyCompactSpace

theorem continuous_brMat : Continuous (brMat (R := Adeles F) m K) := by
  change Continuous fun A : Matrix (Fin K) (Fin K) (Adeles F) =>
    Matrix.reindex (finCongr (by omega : m + 1 + K = m + K + 1))
      (finCongr (by omega : m + 1 + K = m + K + 1)) (lrMatrix (m + 1) K A)
  exact (continuous_lrMatrix (F := F)).matrix_reindex _ _

theorem continuous_brHom : Continuous (brHom F m K) := by
  refine continuous_induced_rng.mpr ?_
  change Continuous fun u : unipotentAdelic F K => brPoint (m := m) (u : Points F K)
  refine (GeneralLinearGroupPoints.adelicHomeomorph F (m + K + 1)).symm.continuous.comp ?_
  refine (Units.continuous_iff.mpr ⟨?_, ?_⟩).comp
    ((GeneralLinearGroupPoints.adelicHomeomorph F K).continuous.comp continuous_subtype_val)
  · exact (continuous_brMat (F := F)).comp Units.continuous_val
  · exact (continuous_brMat (F := F)).comp Units.continuous_coe_inv

theorem continuous_blockHom : Continuous (blockHom F m K) := by
  refine continuous_induced_rng.mpr ?_
  have hM : Continuous fun y : YGroup F m K =>
      brSub (m := m) (K := K) (pointMatrix F (y : Points F (m + K + 1))) :=
    continuous_pi fun i => continuous_pi fun j =>
      ((continuous_pointMatrix (F := F)).comp continuous_subtype_val).matrix_elem _ _
  have hU : Continuous fun y : YGroup F m K =>
      unitriangularUnit (brSub (m := m) (K := K) (pointMatrix F (y : Points F (m + K + 1))))
        (isUnitriangular_brSub (isUnitriangular_yGroup y)) :=
    Units.continuous_iff.mpr ⟨hM, hM.matrix_adjugate⟩
  exact (GeneralLinearGroupPoints.adelicHomeomorph F K).symm.continuous.comp hU

/-- The rectangle coordinates of a point of `Y(𝔸)`. -/
def yCoord (y : YGroup F m K) : ColGroup F (Fin (m + 1) × Fin K) :=
  Multiplicative.ofAdd fun p => pointMatrix F (y : Points F (m + K + 1))
    ⟨p.1, by omega⟩ ⟨m + 1 + p.2, by omega⟩

theorem yCoord_yHom (A : ColGroup F (Fin (m + 1) × Fin K)) : yCoord (yHom F m K A) = A := by
  apply Multiplicative.toAdd.injective
  funext p
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := p
  simp only [yCoord, coe_yHom, pointMatrix_yPoint, Matrix.add_apply, yMat, toAdd_ofAdd]
  rw [Matrix.one_apply_ne (fun h => by have := congrArg Fin.val h; simp at this; omega), zero_add,
    dite_eq_left ⟨Nat.le_of_lt_succ hi, Nat.le_add_right (m + 1) j⟩]
  simp only [Nat.add_sub_cancel_left]

theorem continuous_yPoint :
    Continuous fun A : Fin (m + 1) × Fin K → Adeles F => yPoint (m := m) A := by
  refine (GeneralLinearGroupPoints.adelicHomeomorph F (m + K + 1)).symm.continuous.comp ?_
  have h : Continuous fun A : Fin (m + 1) × Fin K → Adeles F => yMat m K A := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [yMat]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  exact Units.continuous_iff.mpr ⟨continuous_const.add h, continuous_const.sub h⟩

theorem isEmbedding_yHom : IsEmbedding (yHom F m K) := by
  refine Function.LeftInverse.isEmbedding (f := yCoord) yCoord_yHom ?_ ?_
  · exact continuous_ofAdd.comp (continuous_pi fun p =>
      ((continuous_pointMatrix (F := F)).comp continuous_subtype_val).matrix_elem _ _)
  · exact continuous_induced_rng.mpr (continuous_yPoint.comp continuous_toAdd)

end Topology

section Rational

/-- A point of `Y(𝔸)` is rational exactly when it is the image of a rational matrix. -/
theorem mem_rationalY_iff (y : YGroup F m K) :
    y ∈ AdelicSubgroupPoints.rationalSubgroup F (Scheme F (m + K + 1))
        (projectionUnipotent F (m + K + 1) m) ↔
      ∃ M : RationalGL F (m + K + 1), (y : Points F (m + K + 1)) =
        (GeneralLinearGroupPoints.adelicEquiv F (m + K + 1)).symm
          (AdelicGL.rational F (m + K + 1) M) := by
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨GeneralLinearGroupPoints.rationalEquiv F (m + K + 1) q.val, ?_⟩
    apply (GeneralLinearGroupPoints.adelicEquiv F (m + K + 1)).injective
    rw [MulEquiv.apply_symm_apply]
    exact GeneralLinearGroupPoints.adelicEquiv_rational F (m + K + 1) q.val
  · rintro ⟨M, hM⟩
    have hmat : pointMatrix F (y : Points F (m + K + 1)) =
        (M : Matrix (Fin (m + K + 1)) (Fin (m + K + 1)) F).map (algebraMap F (Adeles F)) := by
      rw [hM, pointMatrix_symm_rational]
    have hMu : PrimitiveAdelicHeight.IsUnitriangular
        (M : Matrix (Fin (m + K + 1)) (Fin (m + K + 1)) F) := by
      rw [← isUnitriangular_map_iff, ← hmat]
      exact isUnitriangular_yGroup y
    have hcol : ∀ a b : Fin (m + K + 1), (b : ℕ) ≤ m →
        (M : Matrix (Fin (m + K + 1)) (Fin (m + K + 1)) F) a b =
          (1 : Matrix (Fin (m + K + 1)) (Fin (m + K + 1)) F) a b := by
      intro a b hb
      apply AdeleRing.algebraMap_injective (𝓞 F) F
      have := ((mem_projectionAdelic_iff F m y.val).mp y.property).2 a b hb
      change pointMatrix F (y : Points F (m + K + 1)) a b = _ at this
      rw [hmat, Matrix.map_apply] at this
      rw [this, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    refine ⟨⟨(GeneralLinearGroupPoints.rationalEquiv F (m + K + 1)).symm M,
      (mem_projectionRational_iff F m _).mpr (by
        rw [MulEquiv.apply_symm_apply]
        exact ⟨hMu, hcol⟩)⟩, Subtype.ext ?_⟩
    apply (GeneralLinearGroupPoints.adelicEquiv F (m + K + 1)).injective
    change GeneralLinearGroupPoints.adelicEquiv F (m + K + 1) (AdelicGroupPoints.rational F _
      ((GeneralLinearGroupPoints.rationalEquiv F (m + K + 1)).symm M)) = _
    rw [GeneralLinearGroupPoints.adelicEquiv_rational, hM, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply]

theorem rational_brGL (M : RationalGL F K) :
    AdelicGL.rational F (m + K + 1) (brGL m K M) = brGL m K (AdelicGL.rational F K M) := by
  ext a b
  rw [AdelicGL.rational_apply]
  simp only [brGL, Units.coe_map]
  rw [brMat_apply, brMat_apply]
  simp only [AdelicGL.rational_apply]
  split_ifs <;> simp

theorem brHom_mem_rational {u : unipotentAdelic F K}
    (hu : u ∈ AdelicSubgroupPoints.rationalSubgroup F (Scheme F K) (upperUnipotent F K)) :
    brHom F m K u ∈ AdelicSubgroupPoints.rationalSubgroup F (Scheme F (m + K + 1))
      (projectionUnipotent F (m + K + 1) m) := by
  obtain ⟨M, hM⟩ := (mem_rationalSubgroup_unipotent_iff u).mp hu
  refine (mem_rationalY_iff _).mpr ⟨brGL m K M, ?_⟩
  rw [coe_brHom, hM]
  unfold brPoint
  rw [MulEquiv.apply_symm_apply, rational_brGL]

theorem blockHom_mem_rational {y : YGroup F m K}
    (hy : y ∈ AdelicSubgroupPoints.rationalSubgroup F (Scheme F (m + K + 1))
      (projectionUnipotent F (m + K + 1) m)) :
    blockHom F m K y ∈
      AdelicSubgroupPoints.rationalSubgroup F (Scheme F K) (upperUnipotent F K) := by
  obtain ⟨M, hM⟩ := (mem_rationalY_iff y).mp hy
  have hmat : pointMatrix F (y : Points F (m + K + 1)) =
      (M : Matrix (Fin (m + K + 1)) (Fin (m + K + 1)) F).map (algebraMap F (Adeles F)) := by
    rw [hM, pointMatrix_symm_rational]
  have hMu : PrimitiveAdelicHeight.IsUnitriangular
      (M : Matrix (Fin (m + K + 1)) (Fin (m + K + 1)) F) := by
    rw [← isUnitriangular_map_iff, ← hmat]
    exact isUnitriangular_yGroup y
  refine (mem_rationalSubgroup_unipotent_iff _).mpr
    ⟨unitriangularUnit (brSub (m := m) (K := K)
      (M : Matrix (Fin (m + K + 1)) (Fin (m + K + 1)) F)) (isUnitriangular_brSub hMu), ?_⟩
  apply point_ext
  change pointMatrix F ((blockPoint y : unipotentAdelic F K) : Points F K) = _
  rw [pointMatrix_blockPoint, pointMatrix_symm_rational, hmat]
  ext i j
  rfl

theorem yHom_mem_rational_iff (A : ColGroup F (Fin (m + 1) × Fin K)) :
    yHom F m K A ∈ AdelicSubgroupPoints.rationalSubgroup F (Scheme F (m + K + 1))
        (projectionUnipotent F (m + K + 1) m) ↔
      A ∈ ratLattice F (Fin (m + 1) × Fin K) := by
  constructor
  · intro hA
    obtain ⟨M, hM⟩ := (mem_rationalY_iff _).mp hA
    have hmat := congrArg (pointMatrix F) hM
    rw [coe_yHom, pointMatrix_yPoint, pointMatrix_symm_rational] at hmat
    refine ⟨fun p => (M : Matrix (Fin (m + K + 1)) (Fin (m + K + 1)) F)
      ⟨p.1, by omega⟩ ⟨m + 1 + p.2, by omega⟩, ?_⟩
    funext p
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := p
    have := congrFun (congrFun hmat ⟨i, by omega⟩) ⟨m + 1 + j, by omega⟩
    simp only [Matrix.add_apply, yMat, Matrix.map_apply] at this
    rw [Matrix.one_apply_ne (fun h => by have := congrArg Fin.val h; simp at this; omega),
      zero_add, dite_eq_left ⟨Nat.le_of_lt_succ hi, Nat.le_add_right (m + 1) j⟩] at this
    simp only [Nat.add_sub_cancel_left] at this
    rw [ratVec_apply, ← this]
  · rintro ⟨k, hk⟩
    refine (mem_rationalY_iff _).mpr ⟨sqZeroUnit (yMat m K k) (yMat_mul_yMat k k), ?_⟩
    apply point_ext
    rw [coe_yHom, pointMatrix_yPoint, pointMatrix_symm_rational, hk]
    ext a b
    simp only [Matrix.add_apply, Matrix.map_apply, sqZeroUnit_val, yMat, ratVec_apply, map_add,
      Matrix.one_apply]
    split_ifs <;> simp

end Rational

section Coefficient

variable [CompactSpace (AdeleQuotient F)]

local instance dualRadYLocallyCompact' :
    LocallyCompactSpace (YGroup F m K) :=
  (projectionUnipotentClosed F (m + K + 1) m).locallyCompactSpace

local instance dualRadUnipLocallyCompact' (n : ℕ) : LocallyCompactSpace (unipotentAdelic F n) :=
  (isClosed_upperUnipotent_adelicPoints F n).locallyCompactSpace

/-- **The character coefficient along `Y_(m+K+1,m)` as an iterated period**: the normalized
period over `N_K(F) \ N_K(𝔸)` of the torus integral over the rectangle coordinates. -/
theorem coefficient_eq_iterated (ψ : AddChar (Adeles F) ℂ) (hψc : Continuous ψ)
    (hψF : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1)
    (f : Points F (m + K + 1) → ℂ) (hf : Continuous f)
    (hfΓ : ∀ k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (m + K + 1)), ∀ x, f (k * x) = f x)
    (x : Points F (m + K + 1)) :
    subgroupCharacterCoefficient F (Scheme F (m + K + 1)) (projectionUnipotent F (m + K + 1) m)
        (projectionCharacter F (m + K) m ψ) f x =
      unipotentPeriod F K (fun u =>
        Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin (m + 1) × Fin K) (fun A =>
          f (((yHom F m K (Multiplicative.ofAdd A) * brHom F m K u : YGroup F m K) :
              Points F (m + K + 1)) * x) *
            starRingEnd ℂ (projectionCharacter F (m + K) m ψ
              (yHom F m K (Multiplicative.ofAdd A) * brHom F m K u)))) := by
  have hcpt := compactSpace_projectionRationalQuotient F (r := m + K) m
  have hcpt0 := compactSpace_unipotentRationalQuotient F K
  have hχc := continuous_projectionCharacter F (r := m + K) m ψ hψc
  have hχΛ : ∀ (k : AdelicSubgroupPoints.rationalSubgroup F (Scheme F (m + K + 1))
      (projectionUnipotent F (m + K + 1) m)) (y : YGroup F m K),
      projectionCharacter F (m + K) m ψ (k * y) = projectionCharacter F (m + K) m ψ y := by
    intro k y
    rw [projectionCharacter_mul, projectionCharacter_rational F m ψ hψF _ k.property, one_mul]
  have hf' : ∀ (k : AdelicSubgroupPoints.rationalSubgroup F (Scheme F (m + K + 1))
      (projectionUnipotent F (m + K + 1) m)) (y : Points F (m + K + 1)),
      f (((k : YGroup F m K) : Points F (m + K + 1)) * y) = f y :=
    fun k y => hfΓ _ (coe_mem_rationalSubgroup F k.property) y
  rw [subgroupCharacterCoefficient_eq_setIntegral F (Scheme F (m + K + 1)) _ _ hχc.measurable hχΛ
    f hf.measurable hf' x, quotientMassNormalizer_toReal]
  have hφ : Continuous (fun y : YGroup F m K =>
      f ((y : Points F (m + K + 1)) * x) * starRingEnd ℂ (projectionCharacter F (m + K) m ψ y)) :=
    (hf.comp (continuous_subtype_val.mul continuous_const)).mul
      (Complex.continuous_conj.comp hχc)
  have hφΓ : ∀ k ∈ AdelicSubgroupPoints.rationalSubgroup F (Scheme F (m + K + 1))
      (projectionUnipotent F (m + K + 1) m), ∀ y : YGroup F m K,
      f (((k * y : YGroup F m K)) * x) * starRingEnd ℂ (projectionCharacter F (m + K) m ψ (k * y)) =
        f ((y : Points F (m + K + 1)) * x) *
          starRingEnd ℂ (projectionCharacter F (m + K) m ψ y) := by
    intro k hk y
    rw [Subgroup.coe_mul, mul_assoc, hfΓ _ (coe_mem_rationalSubgroup F hk), projectionCharacter_mul,
      projectionCharacter_rational F m ψ hψF _ hk, one_mul]
  have h := LeftCosetSpace.Semidirect.normalizedPeriod_eq_iterated_of_compact (yHom F m K)
    (brHom F m K) (blockHom F m K) blockHom_brHom exists_yHom_eq blockHom_yHom
    isEmbedding_yHom continuous_brHom continuous_blockHom
    (AdelicSubgroupPoints.rationalSubgroup F (Scheme F (m + K + 1))
      (projectionUnipotent F (m + K + 1) m))
    (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F _ _)
    (AdelicSubgroupPoints.rationalSubgroup F (Scheme F K) (upperUnipotent F K))
    (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F _ _)
    (fun u hu => brHom_mem_rational hu) (fun y hy => blockHom_mem_rational hy)
    (ratLattice F (Fin (m + 1) × Fin K)) (isDiscrete_ratLattice F _) yHom_mem_rational_iff
    _ hφ hφΓ
  refine h.trans ?_
  unfold unipotentPeriod
  congr 1
  refine setIntegral_congr_fun (LeftCosetSpace.measurableSet_fundamentalDomain _ _)
    fun u _ => ?_
  refine normalizedPeriod_ratLattice F (Fin (m + 1) × Fin K) _
    (hφ.comp (isEmbedding_yHom.continuous.mul continuous_const)) ?_
  intro p hp z
  simp only [map_mul, mul_assoc]
  exact hφΓ _ ((yHom_mem_rational_iff p).mpr hp) _

end Coefficient

end Langlands.Global.RankinSelbergGlobal.Unfolding
