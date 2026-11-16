import Langlands.Global.RankinSelberg.EqualAnalyticCentralFibration
import Langlands.Global.RankinSelberg.EqualAnalyticTheta

/-! # Rational rows and the parabolic `P'_n(F)`

For `γ ∈ GL_n(F)`, `n = r + 1`, let `e_n γ` be its last row (`rowOf`).

* `P'_n(F) = Z_n(F) P_n(F)` (`eisensteinParabolic`) is the set of `p` with `e_n p ∈ F e_n`
  (`mem_eisensteinParabolic_iff`), so `P'γ = P'γ'` iff `e_n γ' ∈ F e_n γ`.
* `(q, t) ↦ t e_n q.out` is a bijection `P'_n(F) \ GL_n(F) × F^× ≃ F^n ∖ 0`
  (`cosetRowEquiv`); `F^× ≃ GL_1(F)` (`ratUnitEquiv`).
* The last row of `γ g` is `e_n γ · g`, and scaling by an idele `a` is the action of `ζ(a)`
  (`ideleOf_smul_lastRow`).
-/

noncomputable section
universe u
open NumberField MeasureTheory Set Langlands Langlands.Global
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.Global.RankinSelbergGlobal.EqualAnalytic

local instance rowsSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance rowsSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F] (r : ℕ)

local notation "E" => GeneralLinearGroupPoints.adelicEquiv F
local notation "e" => GeneralLinearGroupPoints.adelicHomeomorph F

/-- The last row `e_n γ` of a rational matrix. -/
def rowOf (c : RationalGL F (r + 1)) : RatRow F (r + 1) :=
  Matrix.of fun _ j => (c : Matrix (Fin (r + 1)) (Fin (r + 1)) F) (Fin.last r) j

omit [NumberField F] in
theorem rowOf_mul (c c' : RationalGL F (r + 1)) :
    rowOf F r (c * c') = rowOf F r c * (c' : Matrix (Fin (r + 1)) (Fin (r + 1)) F) := by
  ext i j
  simp only [rowOf, Units.val_mul, Matrix.mul_apply, Matrix.of_apply]

omit [NumberField F] in
theorem rowOf_one_mul (c : RationalGL F (r + 1)) :
    rowOf F r 1 * (c : Matrix (Fin (r + 1)) (Fin (r + 1)) F) = rowOf F r c := by
  rw [← rowOf_mul, one_mul]

omit [NumberField F] in
theorem rowOf_ne_zero (c : RationalGL F (r + 1)) : rowOf F r c ≠ 0 := by
  intro h
  have hdet : Matrix.det (c : Matrix (Fin (r + 1)) (Fin (r + 1)) F) = 0 :=
    Matrix.det_eq_zero_of_row_eq_zero (Fin.last r) fun j => by
      have := congrFun (congrFun h 0) j
      simpa [rowOf] using this
  exact (Matrix.isUnit_det_of_invertible _ |>.ne_zero) hdet

/-- The subgroup of rational matrices whose last row is a multiple of `e_n`. -/
def lastRowScalarSubgroup : Subgroup (RationalGL F (r + 1)) where
  carrier := {p | ∃ a : F, rowOf F r p = a • rowOf F r 1}
  mul_mem' {p p'} hp hp' := by
    obtain ⟨a, ha⟩ := hp
    obtain ⟨a', ha'⟩ := hp'
    refine ⟨a * a', ?_⟩
    rw [rowOf_mul, ha, Matrix.smul_mul, rowOf_one_mul, ha', smul_smul]
  one_mem' := ⟨1, (one_smul _ _).symm⟩
  inv_mem' {p} hp := by
    obtain ⟨a, ha⟩ := hp
    have h1 : rowOf F r 1 = a • rowOf F r p⁻¹ := by
      rw [← mul_inv_cancel p, rowOf_mul, ha, Matrix.smul_mul, rowOf_one_mul]
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_smul] at h1
      exact rowOf_ne_zero F r 1 h1
    refine ⟨a⁻¹, ?_⟩
    rw [h1, smul_smul, inv_mul_cancel₀ ha0, one_smul]

omit [NumberField F] in
theorem scalar_mem_lastRowScalarSubgroup (u : Fˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) u ∈ lastRowScalarSubgroup F r := by
  refine ⟨(u : F), ?_⟩
  ext i j
  simp only [rowOf, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.of_apply,
    Matrix.smul_apply, Units.val_one, Matrix.diagonal_apply, Matrix.one_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]

omit [NumberField F] in
theorem eisensteinParabolic_eq : eisensteinParabolic F r = lastRowScalarSubgroup F r := by
  apply le_antisymm
  · refine sup_le (fun p hp => ⟨1, ?_⟩) (fun p hp => ?_)
    · ext i j
      have h := hp j
      simp only [rowOf, Matrix.of_apply, one_smul, Units.val_one, Matrix.one_apply]
      rw [h]
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd h1.symm h2
      · exact absurd h2.symm h1
      · rfl
    · rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hp
      obtain ⟨u, rfl⟩ := hp
      exact scalar_mem_lastRowScalarSubgroup F r u
  · rintro p ⟨a, ha⟩
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_smul] at ha
      exact rowOf_ne_zero F r p ha
    set u : Fˣ := Units.mk0 a ha0
    have hp : p = Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) u *
        (Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) u⁻¹ * p) := by
      rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
    rw [hp]
    refine mul_mem (Subgroup.mem_sup_right ?_) (Subgroup.mem_sup_left ?_)
    · rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨u, rfl⟩
    · intro j
      have h := congrFun (congrFun (rowOf_mul F r (Matrix.GeneralLinearGroup.scalar
        (Fin (r + 1)) u⁻¹) p) 0) j
      have h2 : rowOf F r (Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) u⁻¹) =
          ((u⁻¹ : Fˣ) : F) • rowOf F r 1 := by
        ext i k
        simp only [rowOf, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
          Matrix.of_apply, Matrix.smul_apply, Units.val_one, Matrix.diagonal_apply,
          Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      rw [h2, Matrix.smul_mul, rowOf_one_mul, ha, smul_smul] at h
      have h3 : ((u⁻¹ : Fˣ) : F) * a = 1 := by
        simp only [u, Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel₀ ha0]
      rw [h3, one_smul] at h
      change (Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) u⁻¹ * p :
        Matrix (Fin (r + 1)) (Fin (r + 1)) F) (Fin.last r) j = _
      have h4 : rowOf F r (Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) u⁻¹ * p) 0 j =
          (Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) u⁻¹ * p :
            Matrix (Fin (r + 1)) (Fin (r + 1)) F) (Fin.last r) j := rfl
      rw [← h4, h]
      simp only [rowOf, Matrix.of_apply, Units.val_one, Matrix.one_apply]
      split_ifs with h5 h6 h6
      · rfl
      · exact absurd h5.symm h6
      · exact absurd h6.symm h5
      · rfl

omit [NumberField F] in
theorem mem_eisensteinParabolic_iff (p : RationalGL F (r + 1)) :
    p ∈ eisensteinParabolic F r ↔ ∃ a : F, rowOf F r p = a • rowOf F r 1 := by
  rw [eisensteinParabolic_eq]
  rfl

omit [NumberField F] in
/-- `P'γ = P'γ'` iff the last rows are proportional. -/
theorem mk_eq_mk_iff_rowOf (c c' : RationalGL F (r + 1)) :
    LeftCosetSpace.mk (eisensteinParabolic F r) c = LeftCosetSpace.mk (eisensteinParabolic F r) c'
      ↔ ∃ a : F, rowOf F r c' = a • rowOf F r c := by
  rw [LeftCosetSpace.mk_eq_mk_iff, mem_eisensteinParabolic_iff]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have h := congrArg (fun v => v * (c : Matrix (Fin (r + 1)) (Fin (r + 1)) F)) ha
    rwa [← rowOf_mul, inv_mul_cancel_right, Matrix.smul_mul, rowOf_one_mul] at h
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [rowOf_mul, ha, Matrix.smul_mul, ← rowOf_mul, mul_inv_cancel]

omit [NumberField F] in
theorem mk_out (q : LeftCosetSpace (eisensteinParabolic F r)) :
    LeftCosetSpace.mk (eisensteinParabolic F r) (Quotient.out q) = q :=
  Quotient.out_eq q

omit [NumberField F] in
/-- Every nonzero row is the last row of an invertible matrix. -/
theorem exists_rowOf_eq (C : RatRow F (r + 1)) (hC : C ≠ 0) :
    ∃ c : RationalGL F (r + 1), rowOf F r c = C := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, C 0 j ≠ 0 := by
    by_contra h
    push Not at h
    exact hC (by ext i k; rw [Subsingleton.elim i 0]; exact h k)
  set x : Fin (r + 1) → F := fun k => C 0 k
  let τ : Equiv.Perm (Fin (r + 1)) := Equiv.swap j (Fin.last r)
  let M : Matrix (Fin (r + 1)) (Fin (r + 1)) F :=
    ((1 : Matrix (Fin (r + 1)) (Fin (r + 1)) F).updateRow j x).submatrix τ id
  have hsum : (∑ k, x k • (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) F) k) = x := by
    funext i
    simp [Matrix.one_apply]
  have hdet : M.det ≠ 0 := by
    have h1 := Matrix.det_updateRow_sum (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) F) j x
    rw [hsum, Matrix.det_one, smul_eq_mul, mul_one] at h1
    simp only [M, Matrix.det_permute, h1]
    refine mul_ne_zero ?_ hj
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h]
  refine ⟨((Matrix.isUnit_iff_isUnit_det M).mpr (Ne.isUnit hdet)).unit, ?_⟩
  ext i k
  rw [Subsingleton.elim i 0]
  change M (Fin.last r) k = C 0 k
  simp [M, τ, Equiv.swap_apply_right, x]

/-- **`P'_n(F) \ GL_n(F) × F^× ≃ F^n ∖ 0`**, `(q, t) ↦ t e_n q.out`. -/
def cosetRowMap (p : LeftCosetSpace (eisensteinParabolic F r) × Fˣ) :
    {C : RatRow F (r + 1) // C ≠ 0} :=
  ⟨(p.2 : F) • rowOf F r (Quotient.out p.1), by
    intro h
    rcases smul_eq_zero.1 h with h1 | h1
    · exact p.2.ne_zero h1
    · exact rowOf_ne_zero F r _ h1⟩

omit [NumberField F] in
theorem cosetRowMap_bijective : Function.Bijective (cosetRowMap F r) := by
  constructor
  · rintro ⟨q, t⟩ ⟨q', t'⟩ h
    have h1 : (t : F) • rowOf F r (Quotient.out q) = (t' : F) • rowOf F r (Quotient.out q') :=
      congrArg Subtype.val h
    have hq : q = q' := by
      rw [← mk_out F r q, ← mk_out F r q', mk_eq_mk_iff_rowOf]
      refine ⟨((t' : F))⁻¹ * t, ?_⟩
      rw [mul_smul, h1, smul_smul, inv_mul_cancel₀ t'.ne_zero, one_smul]
    subst hq
    have ht : (t : F) = t' := by
      by_contra hne
      have h2 : ((t : F) - t') • rowOf F r (Quotient.out q) = 0 := by
        rw [sub_smul, h1, sub_self]
      rcases smul_eq_zero.1 h2 with h3 | h3
      · exact hne (sub_eq_zero.1 h3)
      · exact rowOf_ne_zero F r _ h3
    rw [Units.ext ht]
  · rintro ⟨C, hC⟩
    obtain ⟨c, hc⟩ := exists_rowOf_eq F r C hC
    set q := LeftCosetSpace.mk (eisensteinParabolic F r) c
    have h1 := (mk_eq_mk_iff_rowOf F r (Quotient.out q) c).1 (mk_out F r q)
    obtain ⟨a, ha⟩ := h1
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_smul, hc] at ha
      exact hC ha
    refine ⟨(q, Units.mk0 a ha0), Subtype.ext ?_⟩
    show a • rowOf F r (Quotient.out q) = C
    rw [← hc, ha]

/-- The bijection `P'_n(F) \ GL_n(F) × F^× ≃ F^n ∖ 0`. -/
def cosetRowEquiv : LeftCosetSpace (eisensteinParabolic F r) × Fˣ ≃
    {C : RatRow F (r + 1) // C ≠ 0} :=
  Equiv.ofBijective (cosetRowMap F r) (cosetRowMap_bijective F r)

omit [NumberField F] in
theorem cosetRowEquiv_apply (p : LeftCosetSpace (eisensteinParabolic F r) × Fˣ) :
    (cosetRowEquiv F r p : RatRow F (r + 1)) = (p.2 : F) • rowOf F r (Quotient.out p.1) := rfl

/-! ### `F^×` inside `𝔸^×` -/

/-- The principal idele of `f ∈ F^×`, as a point of `GL_1(𝔸)`. -/
def ratUnit (f : Fˣ) : Points F 1 :=
  AdelicGroupPoints.rational F (Scheme F 1)
    ((GeneralLinearGroupPoints.rationalEquiv F 1).symm (Matrix.GeneralLinearGroup.scalar (Fin 1) f))

theorem ratUnit_mem (f : Fˣ) : ratUnit F f ∈ ideleRational F := ⟨_, rfl⟩

theorem ideleOf_ratUnit (f : Fˣ) : ideleOf F (ratUnit F f) = diagonalUnits F f := by
  change AdelicGL.determinant F 1 (e 1 (ratUnit F f)) = _
  rw [ratUnit, GeneralLinearGroupPoints.adelicHomeomorph_rational, MulEquiv.apply_symm_apply,
    determinant_rational]
  congr 1
  apply Units.ext
  simp

theorem ratUnit_bijective :
    Function.Bijective fun f : Fˣ => (⟨ratUnit F f, ratUnit_mem F f⟩ : ideleRational F) := by
  constructor
  · intro f f' h
    have h1 := congrArg (fun z : ideleRational F => ideleOf F (z : Points F 1)) h
    simp only [ideleOf_ratUnit] at h1
    apply Units.ext
    have h2 := congrArg (fun u : Ideles F => (u : Adeles F)) h1
    exact algebraMap_adeles_injective F h2
  · rintro ⟨_, c', rfl⟩
    set c₁ := GeneralLinearGroupPoints.rationalEquiv F 1 c'
    refine ⟨Matrix.GeneralLinearGroup.det c₁, Subtype.ext ?_⟩
    show AdelicGroupPoints.rational F (Scheme F 1) ((GeneralLinearGroupPoints.rationalEquiv F 1).symm
      (Matrix.GeneralLinearGroup.scalar (Fin 1) (Matrix.GeneralLinearGroup.det c₁))) =
        AdelicGroupPoints.rational F (Scheme F 1) c'
    congr 1
    rw [MulEquiv.symm_apply_eq]
    apply Units.ext
    ext i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    simp [Matrix.GeneralLinearGroup.coe_scalar, c₁]

/-- `F^× ≃ GL_1(F) ⊆ GL_1(𝔸)`. -/
def ratUnitEquiv : Fˣ ≃ ideleRational F :=
  Equiv.ofBijective _ (ratUnit_bijective F)

theorem ratUnitEquiv_apply (f : Fˣ) : (ratUnitEquiv F f : Points F 1) = ratUnit F f := rfl

/-! ### Last rows of adelic points -/

theorem adelicEquiv_rationalPoint (c : RationalGL F (r + 1)) :
    E (r + 1) (rationalPoint F (r + 1) c) = AdelicGL.rational F (r + 1) c := by
  change e (r + 1) (AdelicGroupPoints.rational F (Scheme F (r + 1))
    ((GeneralLinearGroupPoints.rationalEquiv F (r + 1)).symm c)) = _
  rw [GeneralLinearGroupPoints.adelicHomeomorph_rational, MulEquiv.apply_symm_apply]

theorem lastRow_eq (g : Points F (r + 1)) :
    lastRow F r g = ratRow F (r + 1) (rowOf F r 1) *
      (E (r + 1) g : Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) := by
  ext i j
  simp only [lastRow, rowOf, ratRow, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply,
    Units.val_one, Matrix.one_apply]
  rw [Finset.sum_eq_single (Fin.last r)]
  · simp
  · intro k _ hk
    simp [Ne.symm hk]
  · simp

theorem lastRow_rationalPoint_mul (c : RationalGL F (r + 1)) (g : Points F (r + 1)) :
    lastRow F r (rationalPoint F (r + 1) c * g) = ratRow F (r + 1) (rowOf F r c) *
      (E (r + 1) g : Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) := by
  rw [lastRow_eq, map_mul, adelicEquiv_rationalPoint, Units.val_mul, ← Matrix.mul_assoc]
  congr 1
  show (rowOf F r 1).map (algebraMap F (Adeles F)) *
      (c : Matrix (Fin (r + 1)) (Fin (r + 1)) F).map (algebraMap F (Adeles F)) =
    (rowOf F r c).map (algebraMap F (Adeles F))
  rw [← Matrix.map_mul, rowOf_one_mul]

theorem ratRow_smul (f : F) (C : RatRow F (r + 1)) :
    ratRow F (r + 1) (f • C) = algebraMap F (Adeles F) f • ratRow F (r + 1) C := by
  ext i j
  simp [ratRow]

/-- **The terms of the Eisenstein series as theta terms.** -/
theorem ideleOf_smul_lastRow (f : Fˣ) (c : RationalGL F (r + 1)) (z : Points F 1)
    (g : Points F (r + 1)) :
    (ideleOf F (ratUnit F f * z) : Adeles F) • lastRow F r (rationalPoint F (r + 1) c * g) =
      ratRow F (r + 1) ((f : F) • rowOf F r c) *
        (E (r + 1) (zeta F (r + 1) z * g) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) := by
  rw [lastRow_rationalPoint_mul, ideleOf_mul, ideleOf_ratUnit, map_mul, adelicEquiv_zeta,
    Units.val_mul, ratRow_smul, Units.val_mul]
  change ((algebraMap F (Adeles F) f) * (ideleOf F z : Adeles F)) • _ = _
  rw [Matrix.smul_mul, show ((AdelicGL.scalar F (r + 1) (ideleOf F z) : AdelicGL F (r + 1)) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) =
      Matrix.scalar (Fin (r + 1)) ((ideleOf F z : Ideles F) : Adeles F) from rfl,
    Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, Matrix.mul_smul, smul_smul]

end Langlands.Global.RankinSelbergGlobal.EqualAnalytic
