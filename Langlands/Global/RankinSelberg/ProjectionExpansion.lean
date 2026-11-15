import Langlands.Global.RankinSelberg.ProjectionRadical
import Langlands.Global.RankinSelberg.UnfoldingDualGL
import Langlands.Global.RankinSelberg.UnequalAnalyticPoints

/-! # The Whittaker expansion of the projection, from the Whittaker expansion of cusp forms -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Opposite Topology
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
  PrimitiveAdelicHeight AdelicSubgroupPoints

local instance expansionSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance expansionSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

section Column

variable (F : Type u) [Field F] [NumberField F]

/-- The matrix of an adelic point. -/
abbrev pointMatrix {n : ℕ} (x : Points F n) : Matrix (Fin n) (Fin n) (Adeles F) :=
  ((GeneralLinearGroupPoints.adelicEquiv F n x : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F))

/-- The column subgroup `V_(j+1)`: the block Levi part of `Y_(r+1,j)` relative to
`Y_(r+1,j+1)`. -/
abbrev columnUnipotent (r j : ℕ) : SubgroupFunctor (Scheme F (r + 1)) :=
  leviUnipotent (Fin (r + 1)) (CommRingCat.of F) (projectionWeight (r + 1) j)
    (projectionWeight (r + 1) (j + 1))

variable {r : ℕ} (j : ℕ)

/-- An adelic point lies in `V_(j+1)(𝔸)` exactly when it agrees with the identity outside the
column `j + 1` above row `j + 1`. -/
theorem mem_columnAdelic_iff (x : Points F (r + 1)) :
    x ∈ adelicPoints F (Scheme F (r + 1)) (columnUnipotent F r j) ↔
      ∀ a b : Fin (r + 1), ¬((b : ℕ) = j + 1 ∧ (a : ℕ) ≤ j) →
        pointMatrix F x a b = (1 : Matrix _ _ (Adeles F)) a b := by
  rw [← mem_columnSubgroup_iff]
  exact mem_ofMatrixSubgroups_affinePoints_iff
    (H := fun A => blockUnipotentSubgroup A (projectionWeight (r + 1) j) ⊓
      blockLeviSubgroup A (projectionWeight (r + 1) (j + 1)))
    (hH := fun f _ hg => ⟨map_mem_blockUnipotentSubgroup _ f.hom hg.1,
      map_mem_blockLeviSubgroup _ f.hom hg.2⟩)
    (CommRingCat.of F) (CommAlgCat.of F (AdeleRing (𝓞 F) F)) x

variable {j} (hj : j < r)

/-- The column vector of a point: the entries of column `j + 1` above row `j + 1`. -/
def colVec (x : Points F (r + 1)) : Fin (r + 1) → Adeles F := fun a =>
  if (a : ℕ) < j + 1 then pointMatrix F x a ⟨j + 1, by omega⟩ else 0

theorem isColSupported_colVec (x : Points F (r + 1)) : IsColSupported j (colVec F hj x) := by
  intro a ha
  simp only [colVec]
  rw [ite_eq_right (by omega)]

/-- A point of `V_(j+1)(𝔸)` is `1 + colMatrix` of its column vector. -/
theorem pointMatrix_eq_of_mem_column {x : Points F (r + 1)}
    (hx : x ∈ adelicPoints F (Scheme F (r + 1)) (columnUnipotent F r j)) :
    pointMatrix F x = 1 + colMatrix j (colVec F hj x) := by
  have h := (mem_columnAdelic_iff F j x).mp hx
  ext a b
  rw [Matrix.add_apply, colMatrix_apply]
  by_cases hab : (b : ℕ) = j + 1 ∧ (a : ℕ) ≤ j
  · have hb : b = ⟨j + 1, by omega⟩ := Fin.ext hab.1
    rw [ite_eq_left ⟨by omega, hab.1⟩, Matrix.one_apply_ne (fun h => by subst h; omega), zero_add]
    simp only [colVec]
    rw [ite_eq_left (by omega), hb]
  · rw [h a b hab, ite_eq_right (fun h' => hab ⟨h'.2, by omega⟩), add_zero]

/-- The point `1 + colMatrix c`. -/
def colPoint (c : Fin (r + 1) → Adeles F) : Points F (r + 1) :=
  (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
    (unitriangularUnit (1 + colMatrix j c) (isUnitriangular_one_add_colMatrix j c))

theorem pointMatrix_colPoint (c : Fin (r + 1) → Adeles F) :
    pointMatrix F (colPoint F (j := j) c) = 1 + colMatrix j c := by
  simp only [pointMatrix, colPoint, MulEquiv.apply_symm_apply]
  rfl

theorem colPoint_mem_unipotentAdelic (c : Fin (r + 1) → Adeles F) :
    colPoint F (j := j) c ∈ unipotentAdelic F (r + 1) := by
  rw [mem_unipotentAdelic_iff]
  change IsUnitriangular (pointMatrix F (colPoint F (j := j) c))
  rw [pointMatrix_colPoint]
  exact isUnitriangular_one_add_colMatrix j c

/-- The superdiagonal sum of `1 + colMatrix d` is the entry of `d` in row `j`. -/
theorem sum_superdiag_one_add_colMatrix (d : Fin (r + 1) → Adeles F) :
    ∑ i : Fin r, (1 + colMatrix j d) i.castSucc i.succ = d (Fin.castSucc ⟨j, hj⟩) := by
  rw [Finset.sum_eq_single ⟨j, hj⟩]
  · rw [Matrix.add_apply, Matrix.one_apply_ne (Fin.castSucc_lt_succ).ne, zero_add,
      colMatrix_apply, ite_eq_left ⟨by simp, by simp⟩]
  · intro i _ hi
    rw [Matrix.add_apply, Matrix.one_apply_ne (Fin.castSucc_lt_succ).ne, zero_add,
      colMatrix_apply, ite_eq_right]
    rintro ⟨-, h2⟩
    exact hi (Fin.ext (by simpa using h2))
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The column vector of a point of the shape `1 + colMatrix d` is `d`. -/
theorem colVec_eq_of_pointMatrix_eq {x : Points F (r + 1)} {d : Fin (r + 1) → Adeles F}
    (hd : IsColSupported j d) (hx : pointMatrix F x = 1 + colMatrix j d) :
    colVec F hj x = d := by
  funext a
  simp only [colVec]
  by_cases ha : (a : ℕ) < j + 1
  · have hne : a ≠ ⟨j + 1, by omega⟩ := fun h => by
      have := congrArg Fin.val h
      simp only at this
      omega
    rw [ite_eq_left ha, hx, Matrix.add_apply, Matrix.one_apply_ne hne, zero_add, colMatrix_apply,
      ite_eq_left ⟨ha, rfl⟩]
  · rw [ite_eq_right ha, hd a (by omega)]

/-- Column vectors add under multiplication in `V_(j+1)(𝔸)`. -/
theorem colVec_mul {x y : Points F (r + 1)}
    (hx : x ∈ adelicPoints F (Scheme F (r + 1)) (columnUnipotent F r j))
    (hy : y ∈ adelicPoints F (Scheme F (r + 1)) (columnUnipotent F r j)) :
    colVec F hj (x * y) = colVec F hj x + colVec F hj y := by
  refine colVec_eq_of_pointMatrix_eq F hj (fun a ha => ?_) ?_
  · rw [Pi.add_apply, isColSupported_colVec F hj x a ha, isColSupported_colVec F hj y a ha,
      add_zero]
  · rw [pointMatrix, map_mul, Units.val_mul]
    change pointMatrix F x * pointMatrix F y = _
    rw [pointMatrix_eq_of_mem_column F hj hx, pointMatrix_eq_of_mem_column F hj hy,
      one_add_colMatrix_mul]

/-- The column vector depends continuously on the point. -/
theorem continuous_colVec : Continuous (colVec F hj) := by
  refine continuous_pi fun a => ?_
  simp only [colVec]
  split_ifs
  · exact (Units.continuous_val.comp
      (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).continuous).matrix_elem _ _
  · exact continuous_const

/-- The column vector of a rational point has rational entries. -/
theorem colVec_rational (x : RationalGroupPoints F (Scheme F (r + 1))) (a : Fin (r + 1)) :
    ∃ f : F, colVec F hj (AdelicGroupPoints.rational F (Scheme F (r + 1)) x) a =
      algebraMap F (Adeles F) f := by
  simp only [colVec]
  split_ifs
  · refine ⟨((GeneralLinearGroupPoints.rationalEquiv F (r + 1) x :
      RationalGL F (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) a ⟨j + 1, by omega⟩, ?_⟩
    simp only [pointMatrix, GeneralLinearGroupPoints.adelicEquiv_rational,
      AdelicGL.rational_apply]
  · exact ⟨0, (map_zero _).symm⟩

/-- `diag(g, I)` for a rational `g ∈ GL_k(F)`, as an adelic point of `GL_(r+1)`. -/
def padRational {k : ℕ} (hk : k ≤ r + 1) (g : RationalGL F k) : Points F (r + 1) :=
  (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm (padGL hk (AdelicGL.rational F k g))

omit hj in
theorem pointMatrix_padRational {k : ℕ} (hk : k ≤ r + 1) (g : RationalGL F k) :
    pointMatrix F (padRational F hk g) =
      ((padGL hk (AdelicGL.rational F k g) : AdelicGL F (r + 1)) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) := by
  simp only [pointMatrix, padRational, MulEquiv.apply_symm_apply]

/-- Commuting a column point past `diag(g, I)`. -/
theorem padRational_mul_column (g : RationalGL F (j + 1)) {x : Points F (r + 1)}
    (hx : x ∈ adelicPoints F (Scheme F (r + 1)) (columnUnipotent F r j)) :
    padRational F (by omega : j + 1 ≤ r + 1) g * x =
      colPoint F (j := j) (Matrix.mulVec (pointMatrix F (padRational F (by omega) g))
        (colVec F hj x)) * padRational F (by omega : j + 1 ≤ r + 1) g := by
  apply (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).injective
  apply Units.ext
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul]
  change pointMatrix F (padRational F _ g) * pointMatrix F x =
    pointMatrix F (colPoint F (j := j) _) * pointMatrix F (padRational F _ g)
  rw [pointMatrix_eq_of_mem_column F hj hx, pointMatrix_colPoint, pointMatrix_padRational,
    mul_add, mul_one, add_mul, one_mul,
    padGL_mul_colMatrix j _ (isColSupported_colVec F hj x)]

/-- A column point of a supported vector lies in `V_(j+1)(𝔸)`. -/
theorem colPoint_mem_column (c : Fin (r + 1) → Adeles F) :
    colPoint F (j := j) c ∈ adelicPoints F (Scheme F (r + 1)) (columnUnipotent F r j) := by
  rw [mem_columnAdelic_iff, pointMatrix_colPoint]
  intro a b hab
  rw [Matrix.add_apply, colMatrix_apply, ite_eq_right (fun h => hab ⟨h.2, by omega⟩), add_zero]

omit hj in
/-- Padding commutes with the rational entrywise map. -/
theorem padGL_rational {k : ℕ} (hk : k ≤ r + 1) (g : RationalGL F k) :
    padGL hk (AdelicGL.rational F k g) = AdelicGL.rational F (r + 1) (padGL hk g) := by
  ext a b
  rw [padGL_apply, AdelicGL.rational_apply, padGL_apply]
  split_ifs <;> simp

/-- The character of the column subgroup attached to a rational `g ∈ GL_(j+1)(F)`:
`x ↦ ψ((P c)_j) · conj ψ(c_j)` with `P = diag(g, I)` and `c` the column vector of `x`. -/
def columnTwist (ψ : AddChar (Adeles F) ℂ) (g : RationalGL F (j + 1)) (x : Points F (r + 1)) :
    ℂ :=
  ψ (Matrix.mulVec (pointMatrix F (padRational F (by omega : j + 1 ≤ r + 1) g))
      (colVec F hj x) (Fin.castSucc ⟨j, hj⟩)) *
    starRingEnd ℂ (ψ (colVec F hj x (Fin.castSucc ⟨j, hj⟩)))

theorem continuous_columnTwist (ψ : AddChar (Adeles F) ℂ) (hψ : Continuous ψ)
    (g : RationalGL F (j + 1)) : Continuous (columnTwist F hj ψ g) := by
  have hc := continuous_colVec F hj
  have h1 : Continuous fun x => colVec F hj x (Fin.castSucc ⟨j, hj⟩) :=
    (continuous_apply (Fin.castSucc ⟨j, hj⟩)).comp hc
  have h2 : Continuous fun x => Matrix.mulVec
      (pointMatrix F (padRational F (by omega : j + 1 ≤ r + 1) g)) (colVec F hj x)
        (Fin.castSucc ⟨j, hj⟩) :=
    (continuous_apply (Fin.castSucc ⟨j, hj⟩)).comp (continuous_const.matrix_mulVec hc)
  unfold columnTwist
  exact (hψ.comp h2).mul (Complex.continuous_conj.comp (hψ.comp h1))

theorem columnTwist_mul (ψ : AddChar (Adeles F) ℂ) (g : RationalGL F (j + 1))
    {x y : Points F (r + 1)}
    (hx : x ∈ adelicPoints F (Scheme F (r + 1)) (columnUnipotent F r j))
    (hy : y ∈ adelicPoints F (Scheme F (r + 1)) (columnUnipotent F r j)) :
    columnTwist F hj ψ g (x * y) = columnTwist F hj ψ g x * columnTwist F hj ψ g y := by
  simp only [columnTwist]
  rw [colVec_mul F hj hx hy, Matrix.mulVec_add, Pi.add_apply, Pi.add_apply,
    AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, map_mul]
  ring

/-- The column character is trivial on rational points. -/
theorem columnTwist_rational (ψ : AddChar (Adeles F) ℂ)
    (hψ : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1) (g : RationalGL F (j + 1))
    (x : RationalGroupPoints F (Scheme F (r + 1))) :
    columnTwist F hj ψ g (AdelicGroupPoints.rational F (Scheme F (r + 1)) x) = 1 := by
  choose f hf using colVec_rational F hj x
  have hcv : colVec F hj (AdelicGroupPoints.rational F (Scheme F (r + 1)) x) =
      fun a => algebraMap F (Adeles F) (f a) := funext hf
  simp only [columnTwist]
  rw [hcv, pointMatrix_padRational, padGL_rational]
  have h1 : Matrix.mulVec ((AdelicGL.rational F (r + 1)
      (padGL (by omega : j + 1 ≤ r + 1) g) : AdelicGL F (r + 1)) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F))
      (fun a => algebraMap F (Adeles F) (f a)) (Fin.castSucc ⟨j, hj⟩) =
      algebraMap F (Adeles F) (Matrix.mulVec ((padGL (by omega : j + 1 ≤ r + 1) g :
        RationalGL F (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) f
          (Fin.castSucc ⟨j, hj⟩)) := by
    simp only [Matrix.mulVec, dotProduct, AdelicGL.rational_apply, map_sum, map_mul]
  rw [h1, hψ, hψ, map_one, mul_one]

omit hj in
/-- The last row of `g ∈ GL_(k+1)(F)` is that of the identity. -/
def LastRowStandard {k : ℕ} (g : RationalGL F (k + 1)) : Prop :=
  ∀ b : Fin (k + 1), (g : Matrix (Fin (k + 1)) (Fin (k + 1)) F) (Fin.last k) b =
    (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) F) (Fin.last k) b

/-- Row `j` of `P c` for `P = diag(g, I)`. -/
theorem mulVec_padRational_row (g : RationalGL F (j + 1)) (c : Fin (r + 1) → Adeles F) :
    Matrix.mulVec (pointMatrix F (padRational F (by omega : j + 1 ≤ r + 1) g)) c
        (Fin.castSucc ⟨j, hj⟩) =
      ∑ a : Fin (r + 1), (if h : (a : ℕ) < j + 1 then
        algebraMap F (Adeles F) ((g : Matrix (Fin (j + 1)) (Fin (j + 1)) F) (Fin.last j)
          ⟨a, h⟩) else 0) * c a := by
  simp only [Matrix.mulVec, dotProduct, pointMatrix_padRational]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [padGL_apply, dite_eq_left (show ((Fin.castSucc ⟨j, hj⟩ : Fin (r + 1)) : ℕ) < j + 1 by
    simp)]
  congr 1

omit hj in
/-- For a unitary character, conjugation is evaluation at the negative. -/
theorem conj_addChar_eq (ψ : AddChar (Adeles F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (y : Adeles F) :
    starRingEnd ℂ (ψ y) = ψ (-y) := by
  have h1 : ψ y * ψ (-y) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h2 : ψ y * starRingEnd ℂ (ψ y) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hψ]
    simp
  have h0 : ψ y ≠ 0 := fun h => by rw [h, zero_mul] at h1; exact zero_ne_one h1
  exact mul_left_cancel₀ h0 (h2.trans h1.symm)

/-- With a standard last row the column character is trivial. -/
theorem columnTwist_eq_one (ψ : AddChar (Adeles F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1)
    {g : RationalGL F (j + 1)} (hg : LastRowStandard F g) (x : Points F (r + 1)) :
    columnTwist F hj ψ g x = 1 := by
  simp only [columnTwist]
  rw [mulVec_padRational_row]
  have hsum : ∑ a : Fin (r + 1), (if h : (a : ℕ) < j + 1 then
      algebraMap F (Adeles F) ((g : Matrix (Fin (j + 1)) (Fin (j + 1)) F) (Fin.last j)
        ⟨a, h⟩) else 0) * colVec F hj x a = colVec F hj x (Fin.castSucc ⟨j, hj⟩) := by
    rw [Finset.sum_eq_single (Fin.castSucc ⟨j, hj⟩)]
    · rw [dite_eq_left (show ((Fin.castSucc ⟨j, hj⟩ : Fin (r + 1)) : ℕ) < j + 1 by simp), hg,
        Matrix.one_apply, ite_eq_left (Fin.ext (by simp)), map_one, one_mul]
    · intro a _ ha
      split_ifs with h
      · rw [hg, Matrix.one_apply_ne, map_zero, zero_mul]
        intro h'
        apply ha
        apply Fin.ext
        have := congrArg Fin.val h'
        simp only [Fin.val_last] at this
        simp [this]
      · rw [zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hsum, conj_addChar_eq F ψ hψ, ← AddChar.map_add_eq_mul, add_neg_cancel,
    AddChar.map_zero_eq_one]

/-- With a nonstandard last row the column character is nontrivial on `V_(j+1)(𝔸)`. -/
theorem exists_columnTwist_ne_one (ψ : AddChar (Adeles F) ℂ) (hψ1 : ψ ≠ 1)
    (hψ : ∀ x, ‖ψ x‖ = 1) {g : RationalGL F (j + 1)} (hg : ¬LastRowStandard F g) :
    ∃ x ∈ adelicPoints F (Scheme F (r + 1)) (columnUnipotent F r j),
      columnTwist F hj ψ g x ≠ 1 := by
  simp only [LastRowStandard, not_forall] at hg
  obtain ⟨b, hb⟩ := hg
  obtain ⟨t, ht⟩ := AddChar.ne_one_iff.mp hψ1
  set δ : F := (g : Matrix (Fin (j + 1)) (Fin (j + 1)) F) (Fin.last j) b -
    (1 : Matrix (Fin (j + 1)) (Fin (j + 1)) F) (Fin.last j) b with hδ
  have hδ0 : δ ≠ 0 := sub_ne_zero.mpr hb
  set c : Fin (r + 1) → Adeles F := fun a =>
    if (a : ℕ) = b then algebraMap F (Adeles F) δ⁻¹ * t else 0 with hc
  have hcs : IsColSupported j c := by
    intro a ha
    simp only [hc]
    rw [ite_eq_right (by have := b.isLt; omega)]
  refine ⟨colPoint F (j := j) c, colPoint_mem_column F c, ?_⟩
  have hcv : colVec F hj (colPoint F (j := j) c) = c :=
    colVec_eq_of_pointMatrix_eq F hj hcs (pointMatrix_colPoint F c)
  simp only [columnTwist]
  rw [hcv, mulVec_padRational_row, conj_addChar_eq F ψ hψ, ← AddChar.map_add_eq_mul]
  have hb' : ((Fin.castLE (by omega) b : Fin (r + 1)) : ℕ) < j + 1 := by
    rw [Fin.val_castLE]
    exact b.isLt
  rw [Finset.sum_eq_single (Fin.castLE (by omega) b)]
  · rw [dite_eq_left hb']
    have h1 : c (Fin.castLE (by omega) b) = algebraMap F (Adeles F) δ⁻¹ * t := by
      simp [hc]
    have h2 : c (Fin.castSucc ⟨j, hj⟩) =
        algebraMap F (Adeles F) ((1 : Matrix (Fin (j + 1)) (Fin (j + 1)) F) (Fin.last j) b) *
          (algebraMap F (Adeles F) δ⁻¹ * t) := by
      simp only [hc, Fin.val_castSucc]
      by_cases hjb : j = (b : ℕ)
      · rw [ite_eq_left hjb, Matrix.one_apply, ite_eq_left (Fin.ext (by simp [hjb])), map_one,
          one_mul]
      · rw [ite_eq_right hjb, Matrix.one_apply, ite_eq_right (fun h => hjb (by
          have := congrArg Fin.val h; simpa using this)), map_zero, zero_mul]
    have hfin : (⟨(Fin.castLE (by omega) b : Fin (r + 1)), hb'⟩ : Fin (j + 1)) = b :=
      Fin.ext (by simp)
    rw [hfin, h1, h2]
    have h3 : algebraMap F (Adeles F) ((g : Matrix (Fin (j + 1)) (Fin (j + 1)) F) (Fin.last j) b) *
        (algebraMap F (Adeles F) δ⁻¹ * t) +
        -(algebraMap F (Adeles F) ((1 : Matrix (Fin (j + 1)) (Fin (j + 1)) F) (Fin.last j) b) *
          (algebraMap F (Adeles F) δ⁻¹ * t)) = t := by
      rw [← sub_eq_add_neg, ← sub_mul, ← map_sub, ← hδ, ← mul_assoc, ← map_mul,
        mul_inv_cancel₀ hδ0, map_one, one_mul]
    rw [h3]
    exact ht
  · intro a _ ha
    split_ifs with h
    · rw [show c a = 0 by
        simp only [hc]
        rw [ite_eq_right (fun h' => ha (Fin.ext (by simp [h'])))], mul_zero]
    · rw [zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

variable [CompactSpace (AdeleQuotient F)]

/-- Left translation of a cusp Whittaker function by a column point. -/
theorem cuspWhittaker_colPoint_mul (T : Automorphic.CuspidalOperatorRealization F r)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space)
    (c : Fin (r + 1) → Adeles F) (g : Points F (r + 1)) :
    cuspWhittaker F T ψ v (colPoint F (j := j) c * g) =
      ψ (c (Fin.castSucc ⟨j, hj⟩)) * cuspWhittaker F T ψ v g := by
  have h := cuspWhittaker_mul_left F T ψ hψ v ⟨_, colPoint_mem_unipotentAdelic F (j := j) c⟩ g
  rw [h]
  congr 1
  simp only [genericCharacter, map_one, one_mul]
  congr 1
  change ∑ i : Fin r, pointMatrix F (colPoint F (j := j) c) i.castSucc i.succ = _
  rw [pointMatrix_colPoint, sum_superdiag_one_add_colMatrix F hj]

end Column

local instance columnClosed (F : Type u) [Field F] [NumberField F] (r j : ℕ) :
    IsClosed (adelicPoints F (Scheme F (r + 1)) (columnUnipotent F r j) :
      Set (Points F (r + 1))) :=
  GeneralLinearBlockSemidirect.isClosed_adelicPoints_leviUnipotent F _ _

local instance columnLocallyCompact (F : Type u) [Field F] [NumberField F] (r j : ℕ) :
    LocallyCompactSpace (adelicPoints F (Scheme F (r + 1)) (columnUnipotent F r j)) :=
  (columnClosed F r j).locallyCompactSpace

section Orthogonality

variable (F : Type u) [Field F] [NumberField F]

/-- `V_(j+1)(F) \ V_(j+1)(𝔸)` is compact. -/
theorem compactSpace_columnRationalQuotient (r j : ℕ) :
    CompactSpace (RationalQuotient F (Scheme F (r + 1)) (columnUnipotent F r j)) := by
  have := compactSpace_projectionRationalQuotient F (r := r) j
  exact GeneralLinearBlockSemidirect.leviRationalQuotientCompactSpace F
    (projectionWeight_mono (r := r) j)

variable {r j : ℕ} (hj : j < r)

open scoped Classical in
/-- Orthogonality on `V_(j+1)`: the normalized period of the column character is `1` for a
standard last row and `0` otherwise. -/
theorem normalized_setIntegral_columnTwist (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (g : RationalGL F (j + 1)) :
    ((Measure.haar : Measure (adelicPoints F (Scheme F (r + 1)) (columnUnipotent F r j)))
        (LeftCosetSpace.fundamentalDomain
          (rationalSubgroup F (Scheme F (r + 1)) (columnUnipotent F r j))
          (isDiscrete_rationalSubgroup F _ _))).toReal⁻¹ •
        ∫ m in LeftCosetSpace.fundamentalDomain
            (rationalSubgroup F (Scheme F (r + 1)) (columnUnipotent F r j))
            (isDiscrete_rationalSubgroup F _ _),
          columnTwist F hj ψ g (m : Points F (r + 1)) ∂Measure.haar =
      if LastRowStandard F g then 1 else 0 := by
  have := compactSpace_columnRationalQuotient F r j
  have : IsFiniteMeasure (LeftCosetSpace.haarQuotientMeasure
      (rationalSubgroup F (Scheme F (r + 1)) (columnUnipotent F r j))
      (isDiscrete_rationalSubgroup F _ _)) :=
    rationalQuotientHaarMeasure_isFiniteMeasure F _ _
  have hE0 := LeftCosetSpace.haar_fundamentalDomain_ne_zero
    (rationalSubgroup F (Scheme F (r + 1)) (columnUnipotent F r j))
    (isDiscrete_rationalSubgroup F _ _)
  have hEtop := LeftCosetSpace.haar_fundamentalDomain_ne_top
    (rationalSubgroup F (Scheme F (r + 1)) (columnUnipotent F r j))
    (isDiscrete_rationalSubgroup F _ _)
  split_ifs with hg
  · simp_rw [columnTwist_eq_one F hj ψ hψ.2.2.2 hg]
    rw [setIntegral_const, smul_smul, Measure.real, inv_mul_cancel₀
      (ENNReal.toReal_ne_zero.mpr ⟨hE0, hEtop⟩), one_smul]
  · obtain ⟨x, hx, hθ⟩ := exists_columnTwist_ne_one F hj ψ hψ.2.1 hψ.2.2.2 hg
    have := haar_isMulRightInvariant_of_compactRationalQuotient F (Scheme F (r + 1))
      (columnUnipotent F r j)
    rw [LeftCosetSpace.Semidirect.setIntegral_fundamentalDomain_character_eq_zero
      (rationalSubgroup F (Scheme F (r + 1)) (columnUnipotent F r j))
      (isDiscrete_rationalSubgroup F _ _)
      (fun m => columnTwist F hj ψ g (m : Points F (r + 1)))
      (fun a b => columnTwist_mul F hj ψ g a.property b.property)
      (fun k hk => by
        obtain ⟨q, hq⟩ := hk
        rw [← hq, AdelicSubgroupPoints.rational_coe]
        exact columnTwist_rational F hj ψ hψ.2.2.1 g q.val)
      (m₀ := ⟨x, hx⟩) hθ, smul_zero]

end Orthogonality

section Character

variable (F : Type u) [Field F] [NumberField F]

/-- Elements of a rational subgroup are rational points of the ambient group. -/
theorem coe_mem_rationalSubgroup {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] {U : SubgroupFunctor G} {k : adelicPoints F G U}
    (hk : k ∈ rationalSubgroup F G U) :
    (k : AdelicGroupPoints F G) ∈ AdelicGroupPoints.rationalSubgroup F G := by
  obtain ⟨q, rfl⟩ := hk
  exact ⟨q.val, rfl⟩

variable {r : ℕ} (j : ℕ) (ψ : AddChar (Adeles F) ℂ)

theorem continuous_projectionCharacter (hψ : Continuous ψ) :
    Continuous (projectionCharacter F r j ψ) := by
  unfold projectionCharacter
  refine hψ.comp (continuous_finsetSum _ fun i _ => ?_)
  exact ((Units.continuous_val.comp
    (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).continuous).matrix_elem _ _).comp
      continuous_subtype_val

theorem projectionCharacter_mul (a b : adelicPoints F (Scheme F (r + 1))
    (projectionUnipotent F (r + 1) j)) :
    projectionCharacter F r j ψ (a * b) =
      projectionCharacter F r j ψ a * projectionCharacter F r j ψ b := by
  have ha := ((mem_projectionAdelic_iff F j a.val).mp a.property).1
  have hb := ((mem_projectionAdelic_iff F j b.val).mp b.property).1
  simp only [projectionCharacter]
  rw [← AddChar.map_add_eq_mul, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Subgroup.coe_mul, map_mul, Units.val_mul]
  exact superdiag_mul_of_isUnitriangular ha hb i

theorem projectionCharacter_rational (hψ : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1)
    (k : adelicPoints F (Scheme F (r + 1)) (projectionUnipotent F (r + 1) j))
    (hk : k ∈ rationalSubgroup F (Scheme F (r + 1)) (projectionUnipotent F (r + 1) j)) :
    projectionCharacter F r j ψ k = 1 := by
  obtain ⟨q, rfl⟩ := hk
  simp only [projectionCharacter]
  rw [AdelicSubgroupPoints.rational_coe, GeneralLinearGroupPoints.adelicEquiv_rational]
  simp only [AdelicGL.rational_apply]
  rw [← map_sum]
  exact hψ _

variable {j} (hj : j < r)

/-- The projection character on the column subgroup reads off the entry in row `j`. -/
theorem projectionCharacter_leviInclusion
    (m : adelicPoints F (Scheme F (r + 1)) (columnUnipotent F r j)) :
    projectionCharacter F r j ψ (GeneralLinearBlockSemidirect.leviInclusion F _ _ m) =
      ψ (colVec F hj (m : Points F (r + 1)) (Fin.castSucc ⟨j, hj⟩)) := by
  simp only [projectionCharacter]
  congr 1
  change ∑ i : Fin r, pointMatrix F (m : Points F (r + 1)) i.castSucc i.succ = _
  rw [pointMatrix_eq_of_mem_column F hj m.property, sum_superdiag_one_add_colMatrix F hj]

end Character

section Cosets

variable {K : Type*} [Field K] {j : ℕ}

/-- The entries of `diag(g, 1)`. -/
theorem cornerEmbedding_apply {R : Type*} [CommRing R] {k : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin k) R) (a b : Fin (k + 1)) :
    ((cornerEmbedding k g : Matrix.GeneralLinearGroup (Fin (k + 1)) R) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) R) a b =
      if hi : (a : ℕ) < k then
        (if hj : (b : ℕ) < k then (g : Matrix (Fin k) (Fin k) R) ⟨a, hi⟩ ⟨b, hj⟩ else 0)
      else (if a = b then 1 else 0) := by
  simp only [cornerEmbedding, Units.coe_map, cornerMatrix, MonoidHom.coe_mk,
    OneHom.coe_mk, Matrix.reindex_apply, Matrix.submatrix_apply]
  refine Fin.addCases (fun a₀ => ?_) (fun a₁ => ?_) a <;>
    refine Fin.addCases (fun b₀ => ?_) (fun b₁ => ?_) b <;>
    (simp [Fin.ext_iff, Matrix.one_apply]; try omega)

/-- `diag(g, 1)` is the padding of `g` by one. -/
theorem cornerEmbedding_eq_padGL {R : Type*} [CommRing R] {k : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin k) R) :
    cornerEmbedding k g = padGL (Nat.le_succ k) g := by
  ext a b
  rw [cornerEmbedding_apply, padGL_apply]

/-- Padding in two steps is padding in one step. -/
theorem padGL_padGL {R : Type*} [CommRing R] {k n : ℕ} (h : k + 1 ≤ n)
    (g : Matrix.GeneralLinearGroup (Fin k) R) :
    padGL h (padGL (Nat.le_succ k) g) = padGL (by omega : k ≤ n) g := by
  ext a b
  simp only [padGL_apply]
  split_ifs <;> first | rfl | (exfalso; omega) | simp_all [Fin.ext_iff]

/-- Membership in `N_k(F)` inside `GL_k(F)`. -/
theorem mem_rationalUpperUnipotent_iff (F : Type u) [Field F] [NumberField F] {k : ℕ}
    (g : RationalGL F k) :
    g ∈ rationalUpperUnipotent F k ↔ IsUnitriangular (g : Matrix (Fin k) (Fin k) F) := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_rationalPoints_upperUnipotent_iff F x).mp hx
  · intro hg
    refine ⟨(GeneralLinearGroupPoints.rationalEquiv F k).symm g, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_rationalPoints_upperUnipotent_iff, MulEquiv.apply_symm_apply]
      exact hg
    · simp

/-- Left multiplication by a unitriangular matrix does not change the last row. -/
theorem lastRow_unitriangular_mul {n g : Matrix (Fin (j + 1)) (Fin (j + 1)) K}
    (hn : IsUnitriangular n) (b : Fin (j + 1)) : (n * g) (Fin.last j) b = g (Fin.last j) b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last j)]
  · rw [hn.2, one_mul]
  · intro k _ hk
    rw [show n (Fin.last j) k = 0 from hn.1 (lt_of_le_of_ne (Fin.le_last k) hk), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- An invertible matrix whose last row is that of the identity is `n · diag(g', 1)` with `n`
upper unitriangular. -/
theorem exists_unitriangular_mul_padGL (g : Matrix.GeneralLinearGroup (Fin (j + 1)) K)
    (hg : ∀ b, (g : Matrix (Fin (j + 1)) (Fin (j + 1)) K) (Fin.last j) b =
      (1 : Matrix (Fin (j + 1)) (Fin (j + 1)) K) (Fin.last j) b) :
    ∃ (g' : Matrix.GeneralLinearGroup (Fin j) K) (n : Matrix (Fin (j + 1)) (Fin (j + 1)) K),
      IsUnitriangular n ∧
        n * (padGL (Nat.le_succ j) g' : Matrix (Fin (j + 1)) (Fin (j + 1)) K) =
          (g : Matrix (Fin (j + 1)) (Fin (j + 1)) K) := by
  classical
  set A : Matrix (Fin j) (Fin j) K :=
    (g : Matrix (Fin (j + 1)) (Fin (j + 1)) K).submatrix Fin.castSucc Fin.castSucc with hAdef
  have hdet : (g : Matrix (Fin (j + 1)) (Fin (j + 1)) K).det = A.det := by
    rw [Matrix.det_succ_row _ (Fin.last j), Finset.sum_eq_single (Fin.last j)]
    · rw [hg, Matrix.one_apply_eq, mul_one, Fin.succAbove_last, ← two_mul, Fin.val_last,
        pow_mul, neg_one_sq, one_pow, one_mul]
    · intro k _ hk
      rw [hg, Matrix.one_apply_ne (Ne.symm hk), mul_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hA : IsUnit A.det := hdet ▸ (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
  set g' : Matrix.GeneralLinearGroup (Fin j) K := Matrix.nonsingInvUnit A hA with hg'
  set n : Matrix (Fin (j + 1)) (Fin (j + 1)) K := Matrix.of fun a b =>
    if a = b then 1 else if b = Fin.last j ∧ a ≠ Fin.last j then
      (g : Matrix (Fin (j + 1)) (Fin (j + 1)) K) a b else 0 with hn
  have hnu : IsUnitriangular n := by
    refine ⟨fun a b hab => ?_, fun a => ?_⟩
    · have hab' : b < a := hab
      simp only [hn, Matrix.of_apply]
      rw [ite_eq_right (ne_of_gt hab'), ite_eq_right]
      rintro ⟨rfl, -⟩
      exact absurd (Fin.le_last a) (not_le.mpr hab')
    · simp [hn]
  refine ⟨g', n, hnu, ?_⟩
  ext a b
  rw [Matrix.mul_apply]
  by_cases ha : a = Fin.last j
  · subst ha
    rw [Finset.sum_eq_single (Fin.last j)]
    · rw [hnu.2, one_mul, padGL_apply, dite_eq_right (by simp), hg]
      simp [Matrix.one_apply]
    · intro k _ hk
      simp only [hn, Matrix.of_apply]
      rw [ite_eq_right (Ne.symm hk), ite_eq_right (fun h => h.2 rfl), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have hav : (a : ℕ) < j := by
      have := a.isLt
      have : (a : ℕ) ≠ j := fun h => ha (Fin.ext (by simp [h]))
      omega
    have h1 : n a a = 1 := hnu.2 a
    have h2 : n a (Fin.last j) = (g : Matrix (Fin (j + 1)) (Fin (j + 1)) K) a (Fin.last j) := by
      simp [hn, ha]
    have hP1 : (padGL (Nat.le_succ j) g' : Matrix (Fin (j + 1)) (Fin (j + 1)) K) a b =
        if hb : (b : ℕ) < j then A ⟨a, hav⟩ ⟨b, hb⟩ else 0 := by
      rw [padGL_apply, dite_eq_left hav]
      rfl
    have hP2 : (padGL (Nat.le_succ j) g' : Matrix (Fin (j + 1)) (Fin (j + 1)) K)
        (Fin.last j) b = if Fin.last j = b then 1 else 0 := by
      rw [padGL_apply, dite_eq_right (by simp)]
    rw [Fintype.sum_eq_add a (Fin.last j) ha]
    · rw [h1, h2, one_mul, hP1, hP2]
      by_cases hb : (b : ℕ) < j
      · rw [dite_eq_left hb, ite_eq_right (fun h => by subst h; simp at hb), mul_zero, add_zero]
        rfl
      · have hb' : b = Fin.last j := Fin.ext (by have := b.isLt; simp; omega)
        subst hb'
        rw [dite_eq_right hb, ite_eq_left rfl, mul_one, zero_add]
    · intro k hk
      have h3 : n a k = 0 := by
        simp only [hn, Matrix.of_apply]
        rw [ite_eq_right (Ne.symm hk.1), ite_eq_right (fun h => hk.2 h.1)]
      rw [h3, zero_mul]

end Cosets

section CosetsRational

variable (F : Type u) [Field F] [NumberField F] {j : ℕ}

/-- `N_(j)(F) γ ↦ N_(j+1)(F) diag(γ, 1)`. -/
def cosetPad (j : ℕ) : UnipotentRationalCosets F j → UnipotentRationalCosets F (j + 1) :=
  Quotient.map' (padGL (Nat.le_succ j)) fun a b hab => by
    rw [QuotientGroup.rightRel_apply, mem_rationalUpperUnipotent_iff] at hab ⊢
    rw [← map_inv, ← map_mul]
    exact isUnitriangular_padGL _ _ hab

theorem cosetPad_mk (g : RationalGL F j) :
    cosetPad F j (Quotient.mk _ g) = Quotient.mk _ (padGL (Nat.le_succ j) g) := rfl

theorem cosetPad_injective : Function.Injective (cosetPad F j) := by
  intro q q' h
  induction q using Quotient.inductionOn with | h a => ?_
  induction q' using Quotient.inductionOn with | h b => ?_
  rw [cosetPad_mk, cosetPad_mk] at h
  have hr := (mem_rationalUpperUnipotent_iff F _).mp
    (QuotientGroup.rightRel_apply.mp (Quotient.exact h))
  apply Quotient.sound
  refine QuotientGroup.rightRel_apply.mpr ((mem_rationalUpperUnipotent_iff F _).mpr ?_)
  rw [← map_inv, ← map_mul] at hr
  refine ⟨fun c d hcd => ?_, fun c => ?_⟩
  · have := hr.1 (show (Fin.castSucc d : Fin (j + 1)) < Fin.castSucc c from hcd)
    rw [padGL_apply, dite_eq_left (by simp), dite_eq_left (by simp)] at this
    exact this
  · have := hr.2 (Fin.castSucc c)
    rw [padGL_apply, dite_eq_left (by simp), dite_eq_left (by simp)] at this
    exact this

/-- The cosets with standard last row are exactly the image of `cosetPad`. -/
theorem lastRowStandard_out_iff (q : UnipotentRationalCosets F (j + 1)) :
    LastRowStandard F q.out ↔ q ∈ Set.range (cosetPad F j) := by
  constructor
  · intro hq
    obtain ⟨g', n, hn, hprod⟩ := exists_unitriangular_mul_padGL q.out hq
    refine ⟨Quotient.mk _ g', ?_⟩
    rw [cosetPad_mk, ← Quotient.out_eq q]
    apply Quotient.sound
    refine QuotientGroup.rightRel_apply.mpr ((mem_rationalUpperUnipotent_iff F _).mpr ?_)
    have : (q.out * (padGL (Nat.le_succ j) g')⁻¹ : RationalGL F (j + 1)) =
        unitriangularUnit n hn := by
      apply Units.ext
      rw [Units.val_mul, ← hprod, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        mul_one]
      rfl
    rw [this]
    exact hn
  · rintro ⟨q', rfl⟩
    induction q' using Quotient.inductionOn with | h a => ?_
    rw [cosetPad_mk]
    have hr : QuotientGroup.rightRel (rationalUpperUnipotent F (j + 1))
        (Quotient.mk _ (padGL (Nat.le_succ j) a) : UnipotentRationalCosets F (j + 1)).out
        (padGL (Nat.le_succ j) a) :=
      Quotient.exact (Quotient.out_eq _)
    replace hr := (mem_rationalUpperUnipotent_iff F _).mp (QuotientGroup.rightRel_apply.mp hr)
    intro b
    have key : (Quotient.mk _ (padGL (Nat.le_succ j) a) :
        UnipotentRationalCosets F (j + 1)).out =
        (padGL (Nat.le_succ j) a * (Quotient.mk _ (padGL (Nat.le_succ j) a) :
          UnipotentRationalCosets F (j + 1)).out⁻¹)⁻¹ * padGL (Nat.le_succ j) a := by
      group
    rw [key, Units.val_mul]
    have hinv : IsUnitriangular (((padGL (Nat.le_succ j) a *
        (Quotient.mk _ (padGL (Nat.le_succ j) a) : UnipotentRationalCosets F (j + 1)).out⁻¹)⁻¹ :
          RationalGL F (j + 1)) : Matrix (Fin (j + 1)) (Fin (j + 1)) F) := by
      have h := (rationalUpperUnipotent F (j + 1)).inv_mem
        ((mem_rationalUpperUnipotent_iff F _).mpr hr)
      exact (mem_rationalUpperUnipotent_iff F _).mp h
    rw [lastRow_unitriangular_mul hinv, padGL_apply, dite_eq_right (by simp)]
    simp [Matrix.one_apply]

end CosetsRational

section Step

variable (F : Type u) [Field F] [NumberField F]

/-- `GL_k(F)` is countable: it embeds into the discrete rational subgroup of `GL_k(𝔸)`. -/
instance rationalGLCountable (k : ℕ) : Countable (RationalGL F k) := by
  have := LeftCosetSpace.countable_of_isDiscrete
    (AdelicGroupPoints.rationalSubgroup F (Scheme F k))
    (AdelicGroupPoints.isDiscrete_rationalSubgroup F (Scheme F k))
  let e : RationalGL F k → AdelicGroupPoints.rationalSubgroup F (Scheme F k) := fun g =>
    ⟨AdelicGroupPoints.rational F (Scheme F k)
      ((GeneralLinearGroupPoints.rationalEquiv F k).symm g), ⟨_, rfl⟩⟩
  refine Function.Injective.countable (f := e) fun g g' h => ?_
  have h1 := congrArg (fun z : AdelicGroupPoints.rationalSubgroup F (Scheme F k) =>
    GeneralLinearGroupPoints.adelicEquiv F k z.val) h
  simp only [e, GeneralLinearGroupPoints.adelicEquiv_rational, MulEquiv.apply_symm_apply] at h1
  exact AdelicGL.rational_injective F k h1

instance unipotentRationalCosetsCountable (k : ℕ) : Countable (UnipotentRationalCosets F k) :=
  Quotient.countable

/-- The character coefficient along `Y_(r+1,j)` with the projection character. -/
abbrev projectionCoefficient (r j : ℕ) (ψ : AddChar (Adeles F) ℂ) (f : Points F (r + 1) → ℂ)
    (x : Points F (r + 1)) : ℂ :=
  subgroupCharacterCoefficient F (Scheme F (r + 1)) (projectionUnipotent F (r + 1) j)
    (projectionCharacter F r j ψ) f x

variable [CompactSpace (AdeleQuotient F)] {r j : ℕ} (hj : j < r)

omit [CompactSpace (AdeleQuotient F)] in
/-- One column of the projection: the coefficient along `Y_(r+1,j)` is the normalized period
over `V_(j+1)` of the twisted coefficient along `Y_(r+1,j+1)`. -/
theorem projectionCoefficient_eq_column (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (f : Points F (r + 1) → ℂ) (hf : Continuous f)
    (hfΓ : ∀ k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1)), ∀ x, f (k * x) = f x)
    (x : Points F (r + 1)) :
    projectionCoefficient F r j ψ f x =
      ((Measure.haar : Measure (adelicPoints F (Scheme F (r + 1)) (columnUnipotent F r j)))
          (LeftCosetSpace.fundamentalDomain
            (rationalSubgroup F (Scheme F (r + 1)) (columnUnipotent F r j))
            (isDiscrete_rationalSubgroup F _ _))).toReal⁻¹ •
        ∫ m in LeftCosetSpace.fundamentalDomain
            (rationalSubgroup F (Scheme F (r + 1)) (columnUnipotent F r j))
            (isDiscrete_rationalSubgroup F _ _),
          starRingEnd ℂ (ψ (colVec F hj (m : Points F (r + 1)) (Fin.castSucc ⟨j, hj⟩))) *
            projectionCoefficient F r (j + 1) ψ f ((m : Points F (r + 1)) * x)
          ∂Measure.haar := by
  have := compactSpace_projectionRationalQuotient F (r := r) j
  have := compactSpace_projectionRationalQuotient F (r := r) (j + 1)
  rw [projectionCoefficient, subgroupCharacterCoefficient_eq_levi F (projectionWeight_mono j)
    (projectionCharacter F r j ψ) (continuous_projectionCharacter F j ψ hψ.1)
    (projectionCharacter_mul F j ψ) (projectionCharacter_rational F j ψ hψ.2.2.1) f hf
    (fun k hk y => hfΓ _ (coe_mem_rationalSubgroup F hk) y) x]
  congr 1
  refine setIntegral_congr_fun (LeftCosetSpace.measurableSet_fundamentalDomain _ _) ?_
  intro m _
  simp only
  rw [projectionCharacter_leviInclusion F ψ hj]
  rfl

open scoped Classical in
/-- One step of the column induction: an expansion of the coefficient along `Y_(r+1,j+1)` over
`N_(j+1)(F) \ GL_(j+1)(F)` gives an expansion of the coefficient along `Y_(r+1,j)` over the
cosets with standard last row. -/
theorem hasSum_projectionCoefficient_step (T : Automorphic.CuspidalOperatorRealization F r)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space)
    (hclaim : ∀ y : Points F (r + 1), HasSum (fun q : UnipotentRationalCosets F (j + 1) =>
        cuspWhittaker F T ψ v (padRational F (by omega : j + 1 ≤ r + 1) q.out * y))
      (projectionCoefficient F r (j + 1) ψ (cuspFunction F T v) y))
    (x : Points F (r + 1)) :
    HasSum (fun q : UnipotentRationalCosets F (j + 1) =>
        if LastRowStandard F q.out then
          cuspWhittaker F T ψ v (padRational F (by omega : j + 1 ≤ r + 1) q.out * x) else 0)
      (projectionCoefficient F r j ψ (cuspFunction F T v) x) := by
  have := compactSpace_columnRationalQuotient F r j
  have : IsFiniteMeasure (LeftCosetSpace.haarQuotientMeasure
      (rationalSubgroup F (Scheme F (r + 1)) (columnUnipotent F r j))
      (isDiscrete_rationalSubgroup F _ _)) :=
    rationalQuotientHaarMeasure_isFiniteMeasure F _ _
  set E := LeftCosetSpace.fundamentalDomain
    (rationalSubgroup F (Scheme F (r + 1)) (columnUnipotent F r j))
    (isDiscrete_rationalSubgroup F _ _) with hE
  have hEtop := LeftCosetSpace.haar_fundamentalDomain_ne_top
    (rationalSubgroup F (Scheme F (r + 1)) (columnUnipotent F r j))
    (isDiscrete_rationalSubgroup F _ _)
  have : IsFiniteMeasure ((Measure.haar : Measure (adelicPoints F (Scheme F (r + 1))
      (columnUnipotent F r j))).restrict E) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hEtop.lt_top⟩
  set Wq : UnipotentRationalCosets F (j + 1) → ℂ := fun q =>
    cuspWhittaker F T ψ v (padRational F (by omega : j + 1 ≤ r + 1) q.out * x) with hWq
  rw [projectionCoefficient_eq_column F hj ψ hψ (cuspFunction F T v)
    (continuous_cuspFunction F T v) (fun k hk y => cuspFunction_rational_mul F T v hk y) x]
  -- pointwise expansion of the integrand
  have hpt : ∀ m : adelicPoints F (Scheme F (r + 1)) (columnUnipotent F r j),
      HasSum (fun q : UnipotentRationalCosets F (j + 1) =>
          columnTwist F hj ψ q.out (m : Points F (r + 1)) * Wq q)
        (starRingEnd ℂ (ψ (colVec F hj (m : Points F (r + 1)) (Fin.castSucc ⟨j, hj⟩))) *
          projectionCoefficient F r (j + 1) ψ (cuspFunction F T v)
            ((m : Points F (r + 1)) * x)) := by
    intro m
    have h := (hclaim ((m : Points F (r + 1)) * x)).mul_left
      (starRingEnd ℂ (ψ (colVec F hj (m : Points F (r + 1)) (Fin.castSucc ⟨j, hj⟩))))
    convert h using 1
    funext q
    rw [hWq, ← mul_assoc, padRational_mul_column F hj q.out m.property, mul_assoc,
      cuspWhittaker_colPoint_mul F hj T ψ hψ v]
    simp only [columnTwist]
    ring
  have hnorm : ∀ (q : UnipotentRationalCosets F (j + 1)) (y : Points F (r + 1)),
      ‖columnTwist F hj ψ q.out y‖ = 1 := by
    intro q y
    simp only [columnTwist]
    rw [norm_mul, Complex.norm_conj, hψ.2.2.2, hψ.2.2.2, one_mul]
  have hsumm : Summable fun q => ‖Wq q‖ := summable_norm_iff.mpr (hclaim x).summable
  have hint : HasSum (fun q : UnipotentRationalCosets F (j + 1) =>
        ∫ m in E, columnTwist F hj ψ q.out (m : Points F (r + 1)) * Wq q ∂Measure.haar)
      (∫ m in E, starRingEnd ℂ (ψ (colVec F hj (m : Points F (r + 1))
        (Fin.castSucc ⟨j, hj⟩))) *
          projectionCoefficient F r (j + 1) ψ (cuspFunction F T v) ((m : Points F (r + 1)) * x)
        ∂Measure.haar) :=
    hasSum_integral_of_dominated_convergence (fun q _ => ‖Wq q‖)
      (fun q => (((continuous_columnTwist F hj ψ hψ.1 q.out).comp
        continuous_subtype_val).mul continuous_const).aestronglyMeasurable)
      (fun q => ae_of_all _ fun m => by rw [norm_mul, hnorm, one_mul])
      (ae_of_all _ fun _ => hsumm) (integrable_const _) (ae_of_all _ hpt)
  have h2 := hint.const_smul
    ((Measure.haar : Measure (adelicPoints F (Scheme F (r + 1)) (columnUnipotent F r j)))
      E).toReal⁻¹
  convert h2 using 1
  funext q
  rw [integral_mul_const, ← smul_mul_assoc, normalized_setIntegral_columnTwist F hj ψ hψ q.out]
  split_ifs <;> simp [hWq]

omit [CompactSpace (AdeleQuotient F)] in
theorem padRational_mul {k : ℕ} (hk : k ≤ r + 1) (a b : RationalGL F k) :
    padRational F hk (a * b) = padRational F hk a * padRational F hk b := by
  simp only [padRational, map_mul]

omit [CompactSpace (AdeleQuotient F)] in
theorem padRational_padGL {k : ℕ} (hk : k + 1 ≤ r + 1) (g : RationalGL F k) :
    padRational F hk (padGL (Nat.le_succ k) g) = padRational F (Nat.le_of_succ_le hk) g := by
  simp only [padRational]
  rw [padGL_rational, padGL_rational, padGL_padGL]

/-- `W` is left invariant under padded rational unipotent elements. -/
theorem cuspWhittaker_padRational_unipotent_mul (T : Automorphic.CuspidalOperatorRealization F r)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space)
    {k : ℕ} (hk : k ≤ r + 1) {n : RationalGL F k} (hn : n ∈ rationalUpperUnipotent F k)
    (z : Points F (r + 1)) :
    cuspWhittaker F T ψ v (padRational F hk n * z) = cuspWhittaker F T ψ v z := by
  have hu : IsUnitriangular (pointMatrix F (padRational F hk n)) := by
    rw [pointMatrix_padRational, padGL_rational]
    exact (isUnitriangular_padGL hk _ ((mem_rationalUpperUnipotent_iff F n).mp hn)).map _
  have hmem : padRational F hk n ∈ unipotentAdelic F (r + 1) := by
    rw [mem_unipotentAdelic_iff]
    exact hu
  rw [cuspWhittaker_mul_left F T ψ hψ v ⟨_, hmem⟩ z]
  convert one_mul _
  simp only [genericCharacter, map_one, one_mul]
  change ψ (∑ i : Fin r, pointMatrix F (padRational F hk n) i.castSucc i.succ) = 1
  rw [pointMatrix_padRational, padGL_rational]
  simp only [AdelicGL.rational_apply]
  rw [← map_sum]
  exact hψ.2.2.1 _

/-- `W(diag(g, I) x)` depends only on the coset `N_k(F) g`. -/
theorem cuspWhittaker_padRational_of_rightRel (T : Automorphic.CuspidalOperatorRealization F r)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space)
    {k : ℕ} (hk : k ≤ r + 1) {a b : RationalGL F k}
    (hab : QuotientGroup.rightRel (rationalUpperUnipotent F k) a b) (z : Points F (r + 1)) :
    cuspWhittaker F T ψ v (padRational F hk b * z) =
      cuspWhittaker F T ψ v (padRational F hk a * z) := by
  have h := QuotientGroup.rightRel_apply.mp hab
  have hb : b = (b * a⁻¹) * a := by group
  rw [hb, padRational_mul, mul_assoc, cuspWhittaker_padRational_unipotent_mul F T ψ hψ v hk h]

/-- The column induction step on the coset level: an expansion over `N_(j+1)(F) \ GL_(j+1)(F)`
of the coefficient along `Y_(r+1,j+1)` gives an expansion over `N_j(F) \ GL_j(F)` of the
coefficient along `Y_(r+1,j)`. -/
theorem hasSum_projectionCoefficient_succ (T : Automorphic.CuspidalOperatorRealization F r)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space)
    (hclaim : ∀ y : Points F (r + 1), HasSum (fun q : UnipotentRationalCosets F (j + 1) =>
        cuspWhittaker F T ψ v (padRational F (by omega : j + 1 ≤ r + 1) q.out * y))
      (projectionCoefficient F r (j + 1) ψ (cuspFunction F T v) y))
    (x : Points F (r + 1)) :
    HasSum (fun q : UnipotentRationalCosets F j =>
        cuspWhittaker F T ψ v (padRational F (by omega : j ≤ r + 1) q.out * x))
      (projectionCoefficient F r j ψ (cuspFunction F T v) x) := by
  classical
  have h := hasSum_projectionCoefficient_step F hj T ψ hψ v hclaim x
  rw [← (cosetPad_injective F).hasSum_iff (fun q hq => by
    rw [ite_eq_right (fun h' => hq ((lastRowStandard_out_iff F q).mp h'))])] at h
  convert h using 1
  funext q
  simp only [Function.comp]
  rw [ite_eq_left ((lastRowStandard_out_iff F _).mpr ⟨q, rfl⟩)]
  induction q using Quotient.inductionOn with | h a => ?_
  have h1 : QuotientGroup.rightRel (rationalUpperUnipotent F (j + 1))
      (padGL (Nat.le_succ j) a) (cosetPad F j (Quotient.mk _ a)).out := by
    rw [cosetPad_mk]
    exact Quotient.exact (Quotient.out_eq _).symm
  have h2 : QuotientGroup.rightRel (rationalUpperUnipotent F j) a
      (Quotient.mk _ a : UnipotentRationalCosets F j).out :=
    Quotient.exact (Quotient.out_eq _).symm
  rw [cuspWhittaker_padRational_of_rightRel F T ψ hψ v _ h1, padRational_padGL,
    cuspWhittaker_padRational_of_rightRel F T ψ hψ v _ h2]

end Step

section Base

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}

omit [CompactSpace (AdeleQuotient F)] in
/-- `Y_(r+1,r)` is trivial, so its coefficient is evaluation. -/
theorem projectionCoefficient_top (ψ : AddChar (Adeles F) ℂ) (f : Points F (r + 1) → ℂ)
    (x : Points F (r + 1)) : projectionCoefficient F r r ψ f x = f x := by
  have htriv : ∀ y : adelicPoints F (Scheme F (r + 1)) (projectionUnipotent F (r + 1) r),
      y = 1 := by
    intro y
    obtain ⟨-, hcol⟩ := (mem_projectionAdelic_iff F r y.val).mp y.property
    apply Subtype.ext
    apply (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).injective
    apply Units.ext
    ext a b
    rw [hcol a b (by have := b.isLt; omega)]
    simp
  have := compactSpace_projectionRationalQuotient F (r := r) r
  have := normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F (Scheme F (r + 1))
    (projectionUnipotent F (r + 1) r)
  have hχ : projectionCharacter F r r ψ 1 = 1 := by
    simp only [projectionCharacter, OneMemClass.coe_one, map_one, Units.val_one]
    rw [Finset.sum_eq_zero (fun i _ => Matrix.one_apply_ne (Fin.castSucc_lt_succ).ne),
      AddChar.map_zero_eq_one]
  rw [projectionCoefficient, subgroupCharacterCoefficient]
  simp_rw [htriv]
  rw [hχ, map_one, mul_one, OneMemClass.coe_one, one_mul, integral_const, probReal_univ,
    one_smul]

/-- The Whittaker expansion of the vectors of an actual cuspidal realization: for every standard
`ψ`, vector `v` and `g`, the family `γ ↦ W(diag(γ, 1) g)` over `N_r(F) \ GL_r(F)` is absolutely
summable with sum `φ(g)` (Cogdell 2004, Theorem 1.1; Library `WhittakerExpansionStatement`). -/
def CuspidalWhittakerExpansion (T : Automorphic.CuspidalOperatorRealization F r) : Prop :=
  ∀ (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
    ∀ (v : T.Space) (g : Points F (r + 1)),
      Summable (fun q : UnipotentRationalCosets F r =>
          ‖cuspWhittaker F T ψ v (cornerAdelicPoint F r q.out * g)‖) ∧
        HasSum (fun q : UnipotentRationalCosets F r =>
          cuspWhittaker F T ψ v (cornerAdelicPoint F r q.out * g)) (cuspFunction F T v g)

omit [CompactSpace (AdeleQuotient F)] in
theorem padRational_eq_cornerAdelicPoint (g : RationalGL F r) :
    padRational F (Nat.le_succ r) g = cornerAdelicPoint F r g := by
  simp only [padRational, cornerAdelicPoint]
  rw [padGL_rational, cornerEmbedding_eq_padGL]

/-- Every column coefficient has its expansion, by downward induction from the top. -/
theorem hasSum_projectionCoefficient (T : Automorphic.CuspidalOperatorRealization F r)
    (hT : CuspidalWhittakerExpansion F T) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space) :
    ∀ (d j : ℕ) (hjr : j + d = r) (x : Points F (r + 1)),
      HasSum (fun q : UnipotentRationalCosets F j =>
          cuspWhittaker F T ψ v (padRational F (by omega : j ≤ r + 1) q.out * x))
        (projectionCoefficient F r j ψ (cuspFunction F T v) x) := by
  intro d
  induction d with
  | zero =>
    intro j hjr x
    rw [Nat.add_zero] at hjr
    subst hjr
    rw [projectionCoefficient_top]
    convert (hT ψ hψ v x).2 using 1
    funext q
    rw [padRational_eq_cornerAdelicPoint]
  | succ d ih =>
    intro j hjr x
    exact hasSum_projectionCoefficient_succ F (by omega : j < r) T ψ hψ v
      (fun y => ih (j + 1) (by omega) y) x

end Base

section Transfer

variable (F : Type u) [Field F] [NumberField F]

theorem rational_injective (m : ℕ) :
    Function.Injective (AdelicGroupPoints.rational F (Scheme F m)) := by
  intro a b h
  have h1 := congrArg (GeneralLinearGroupPoints.adelicEquiv F m) h
  rw [GeneralLinearGroupPoints.adelicEquiv_rational,
    GeneralLinearGroupPoints.adelicEquiv_rational] at h1
  exact (GeneralLinearGroupPoints.rationalEquiv F m).injective
    (AdelicGL.rational_injective F m h1)

/-- The rational points of `GL_m(𝔸)` as rational matrices. -/
def rationalSubgroupEquiv (m : ℕ) :
    AdelicGroupPoints.rationalSubgroup F (Scheme F m) ≃* RationalGL F m :=
  (MonoidHom.ofInjective (rational_injective F m)).symm.trans
    (GeneralLinearGroupPoints.rationalEquiv F m)

theorem adelicEquiv_rationalSubgroupEquiv (m : ℕ)
    (k : AdelicGroupPoints.rationalSubgroup F (Scheme F m)) :
    AdelicGL.rational F m (rationalSubgroupEquiv F m k) =
      GeneralLinearGroupPoints.adelicEquiv F m k := by
  obtain ⟨x, hx⟩ := k.property
  have hsymm : (MonoidHom.ofInjective (rational_injective F m)).symm k = x :=
    (MulEquiv.symm_apply_eq _).mpr (Subtype.ext hx.symm)
  have h1 : rationalSubgroupEquiv F m k = GeneralLinearGroupPoints.rationalEquiv F m x := by
    show GeneralLinearGroupPoints.rationalEquiv F m
      ((MonoidHom.ofInjective (rational_injective F m)).symm k) = _
    rw [hsymm]
  rw [h1, ← hx, GeneralLinearGroupPoints.adelicEquiv_rational]

omit [NumberField F] in
theorem isUnitriangular_map_iff {m : ℕ} [NumberField F] (M : Matrix (Fin m) (Fin m) F) :
    IsUnitriangular (M.map (algebraMap F (Adeles F))) ↔ IsUnitriangular M := by
  refine ⟨fun h => ⟨fun a b hab => ?_, fun a => ?_⟩, fun h => h.map _⟩
  · apply AdeleRing.algebraMap_injective (𝓞 F) F
    rw [map_zero]
    exact h.1 hab
  · apply AdeleRing.algebraMap_injective (𝓞 F) F
    rw [map_one]
    exact h.2 a

/-- The two descriptions of `N_m(F) \ GL_m(F)` agree. -/
def rationalCosetIndexEquiv (m : ℕ) : RationalCosetIndex F m ≃ UnipotentRationalCosets F m :=
  Quotient.congr (rationalSubgroupEquiv F m).toEquiv fun a b => by
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf,
      mem_unipotentRationalImage_iff_mem_inf, mem_rationalUpperUnipotent_iff,
      MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, ← map_inv, ← map_mul,
      ← isUnitriangular_map_iff F, mem_unipotentAdelic_iff]
    have h := adelicEquiv_rationalSubgroupEquiv F m (b * a⁻¹)
    simp only [AdelicGL.rational, Matrix.GeneralLinearGroup.map] at h
    constructor
    · rintro ⟨-, hu⟩
      rw [← congrArg Units.val h] at hu
      exact hu
    · intro hu
      refine ⟨(b * a⁻¹).property, ?_⟩
      rw [← congrArg Units.val h]
      exact hu

theorem pad_coe_rationalSubgroup {m r : ℕ} (h : m ≤ r + 1)
    (k : AdelicGroupPoints.rationalSubgroup F (Scheme F m)) :
    pad F h (k : Points F m) = padRational F h (rationalSubgroupEquiv F m k) := by
  simp only [pad, padRational]
  rw [adelicEquiv_rationalSubgroupEquiv]

end Transfer

section Expansion

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- **The Whittaker expansion of the projection from that of the cusp form.** If the vectors of
`T` have their Whittaker expansions over `N_r(F) \ GL_r(F)`, then the projection has its
expansion over `N_m(F) \ GL_m(F)` (Cogdell 2004, p.205). -/
theorem projectionWhittakerExpansion_of_cuspidalWhittakerExpansion {r t : ℕ} (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r) (hT : CuspidalWhittakerExpansion F T) :
    ProjectionWhittakerExpansion F h T := by
  intro ψ hψ v g
  have hc := hasSum_projectionCoefficient F T hT ψ hψ v (r - (t + 1)) (t + 1) (by omega)
    (pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) g)
  rw [← (rationalCosetIndexEquiv F (t + 1)).hasSum_iff] at hc
  unfold projection
  rw [UnequalAnalytic.detPower_pad, UnequalAnalytic.pad_pad]
  refine HasSum.mul_left _ ?_
  convert hc using 1
  funext q
  simp only [Function.comp]
  rw [rationalCosetRep, cosetRep, pad_mul, pad_coe_rationalSubgroup]
  have hrel : QuotientGroup.rightRel (rationalUpperUnipotent F (t + 1))
      (rationalSubgroupEquiv F (t + 1) q.out) (rationalCosetIndexEquiv F (t + 1) q).out := by
    have : rationalCosetIndexEquiv F (t + 1) q =
        Quotient.mk _ (rationalSubgroupEquiv F (t + 1) q.out) := by
      conv_lhs => rw [← Quotient.out_eq q]
      rfl
    rw [this]
    exact Quotient.exact (Quotient.out_eq _).symm
  rw [cuspWhittaker_padRational_of_rightRel F T ψ hψ v _ hrel]

end Expansion

end Langlands.Global.RankinSelbergGlobal.Unfolding
