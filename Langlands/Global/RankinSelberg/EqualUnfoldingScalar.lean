import Langlands.Global.RankinSelberg.EqualUnfoldingKernel

/-! # Scalar points and the rational parabolic in the equal-rank unfolding -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal Pointwise
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.EqualUnfolding

open Langlands.Global Unfolding

local instance equalScalarSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance equalScalarSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

section Idele

/-- `z ↦ det z`, from `GL_1(𝔸)` to `𝔸^×`, as a monoid homomorphism; its values are the
Library's `ideleOf`. -/
def ideleOfHom : Points F 1 →* IdeleGroup (𝓞 F) F :=
  Matrix.GeneralLinearGroup.det.comp (GeneralLinearGroupPoints.adelicEquiv F 1).toMonoidHom

theorem ideleOfHom_apply (z : Points F 1) : ideleOfHom F z = ideleOf F z := rfl

theorem ideleOf_mul (z w : Points F 1) : ideleOf F (z * w) = ideleOf F z * ideleOf F w :=
  map_mul (ideleOfHom F) z w

theorem ideleOf_inv (z : Points F 1) : ideleOf F z⁻¹ = (ideleOf F z)⁻¹ :=
  map_inv (ideleOfHom F) z

theorem ideleOf_one : ideleOf F 1 = 1 :=
  map_one (ideleOfHom F)

theorem continuous_ideleOf : Continuous (ideleOf F) :=
  (AdelicGL.determinant F 1).continuous.comp
    (GeneralLinearGroupPoints.adelicHomeomorph F 1).continuous

theorem ideleOf_injective : Function.Injective (ideleOf F) := by
  intro z w h
  apply (GeneralLinearGroupPoints.adelicEquiv F 1).injective
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have h' := congrArg Units.val h
  simp only [ideleOf, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_unique] at h'
  rw [Subsingleton.elim i default, Subsingleton.elim j default]
  exact h'

theorem exists_ideleOf_eq (a : IdeleGroup (𝓞 F) F) : ∃ z : Points F 1, ideleOf F z = a := by
  refine ⟨(GeneralLinearGroupPoints.adelicEquiv F 1).symm
    (Matrix.GeneralLinearGroup.scalar (Fin 1) a), ?_⟩
  apply Units.ext
  simp [ideleOf]

/-- The determinant norm of `z ∈ GL_1(𝔸)` is the idele norm of `det z`. -/
theorem detNorm_one_eq (z : Points F 1) :
    detNorm F 1 z = ((IdeleAbsoluteValue.full F (ideleOf F z) : NNReal) : ℝ) := rfl

/-- The idele of a rational point of `GL_1` is principal. -/
theorem ideleOf_rationalPoint (g : RationalGL F 1) :
    ideleOf F (rationalPoint F 1 g) =
      IdeleGroup.unitEmbedding (𝓞 F) F (Matrix.GeneralLinearGroup.det g) := by
  apply Units.ext
  simp only [ideleOf, adelicEquiv_rationalPoint, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.det_unique, AdelicGL.rational_apply]
  change _ = algebraMap F (AdeleRing (𝓞 F) F) (Matrix.GeneralLinearGroup.det g : F)
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_unique]

theorem centralIdeleCharacter_ideleOf_rational (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    {b : Points F 1} (hb : b ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F 1)) :
    Automorphic.centralIdeleCharacter F χ (ideleOf F b) = 1 := by
  obtain ⟨g, rfl⟩ := exists_rationalPoint_eq F 1 hb
  rw [ideleOf_rationalPoint, Automorphic.centralIdeleCharacter_principal]

end Idele

section ScalarPoint

variable (r : ℕ)

/-- The scalar matrix `diag(a, …, a) ∈ GL_n(𝔸)`, `n = r + 1`, of the idele `a = det z` of
`z ∈ GL_1(𝔸)`. -/
def scalarPoint : Points F 1 →* Points F (r + 1) :=
  (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm.toMonoidHom.comp
    ((Matrix.GeneralLinearGroup.scalar (Fin (r + 1))).comp (ideleOfHom F))

theorem adelicEquiv_scalarPoint (z : Points F 1) :
    GeneralLinearGroupPoints.adelicEquiv F (r + 1) (scalarPoint F r z) =
      Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) (ideleOf F z) := by
  change GeneralLinearGroupPoints.adelicEquiv F (r + 1)
    ((GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm _) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem continuous_scalarPoint : Continuous (scalarPoint F r) :=
  (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).symm.continuous.comp
    ((AdelicGL.scalar F (r + 1)).continuous.comp (continuous_ideleOf F))

theorem scalarPoint_commute (z : Points F 1) (x : Points F (r + 1)) :
    scalarPoint F r z * x = x * scalarPoint F r z := by
  apply (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).injective
  rw [map_mul, map_mul, adelicEquiv_scalarPoint]
  exact AdelicGL.scalar_commute F (r + 1) _ _

theorem scalarPoint_mem_center (z : Points F 1) :
    scalarPoint F r z ∈ Subgroup.center (Points F (r + 1)) :=
  Subgroup.mem_center_iff.mpr fun x => (scalarPoint_commute F r z x).symm

theorem scalarPoint_injective : Function.Injective (scalarPoint F r) := by
  intro z w h
  apply ideleOf_injective F
  have h' := congrArg (fun x => GeneralLinearGroupPoints.adelicEquiv F (r + 1) x) h
  simp only [adelicEquiv_scalarPoint] at h'
  apply Units.ext
  have := congrArg (fun g : Matrix.GeneralLinearGroup (Fin (r + 1)) (Adeles F) =>
    (g : Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) 0 0) h'
  simpa using this

/-- Every central point of `GL_n(𝔸)` is a scalar point. -/
theorem exists_scalarPoint_eq {c : Points F (r + 1)}
    (hc : c ∈ Subgroup.center (Points F (r + 1))) : ∃ z : Points F 1, scalarPoint F r z = c := by
  set e := GeneralLinearGroupPoints.adelicEquiv F (r + 1)
  have he : e c ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin (r + 1)) (Adeles F)) := by
    refine Subgroup.mem_center_iff.mpr fun g => ?_
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hc y]
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at he
  obtain ⟨a, ha⟩ := he
  obtain ⟨z, rfl⟩ := exists_ideleOf_eq F a
  refine ⟨z, e.injective ?_⟩
  rw [adelicEquiv_scalarPoint, ha]

/-- Left multiplication by `diag(a, …, a)` multiplies the last row by `a`. -/
theorem lastRow_scalarPoint_mul (z : Points F 1) (x : Points F (r + 1)) :
    lastRow F r (scalarPoint F r z * x) = (ideleOf F z : Adeles F) • lastRow F r x := by
  ext i j
  simp only [lastRow, Matrix.of_apply, map_mul, adelicEquiv_scalarPoint, Units.val_mul,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.smul_apply, smul_eq_mul]
  rw [Matrix.scalar_apply, Matrix.diagonal_mul]

theorem detNorm_scalarPoint (z : Points F 1) :
    detNorm F (r + 1) (scalarPoint F r z) = detNorm F 1 z ^ (r + 1) := by
  have hdet : Matrix.GeneralLinearGroup.det
      (GeneralLinearGroupPoints.adelicEquiv F (r + 1) (scalarPoint F r z)) =
        ideleOf F z ^ (r + 1) := by
    apply Units.ext
    rw [adelicEquiv_scalarPoint, Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.GeneralLinearGroup.coe_scalar, Units.val_pow_eq_pow_val]
    simp [Matrix.det_diagonal, Matrix.scalar_apply]
  simp only [detNorm, AdelicBlockDeterminantCharacter.determinantNorm]
  change ((IdeleAbsoluteValue.full F (Matrix.GeneralLinearGroup.det
    (GeneralLinearGroupPoints.adelicEquiv F (r + 1) (scalarPoint F r z))) : NNReal) : ℝ) = _
  rw [hdet, map_pow, Units.val_pow_eq_pow_val, NNReal.coe_pow]
  rfl

theorem detPower_scalarPoint (z : Points F 1) (s : ℂ) :
    detPower F (r + 1) (scalarPoint F r z) s = detPower F 1 z ((r + 1 : ℂ) * s) := by
  simp only [detPower, detNorm_scalarPoint, Real.log_pow]
  congr 1
  push_cast
  ring

/-- The scalar point of a rational point of `GL_1` is the rational scalar point. -/
theorem scalarPoint_rationalPoint (g : RationalGL F 1) :
    scalarPoint F r (rationalPoint F 1 g) =
      rationalPoint F (r + 1)
        (Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) (Matrix.GeneralLinearGroup.det g)) := by
  apply (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).injective
  rw [adelicEquiv_scalarPoint, adelicEquiv_rationalPoint, ideleOf_rationalPoint]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Matrix.GeneralLinearGroup.coe_scalar, AdelicGL.rational_apply,
    Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp [IdeleGroup.unitEmbedding, Units.coe_map]

omit [NumberField F] in
/-- The scalar `1 × 1` matrix `a` has determinant `a`. -/
theorem det_scalar_one (a : Fˣ) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) a) = a := by
  apply Units.ext
  simp

end ScalarPoint

section Parabolic

variable (r : ℕ)

/-- The rational parabolic `P'_n(F) = Z_n(F) P_n(F)`, `n = r + 1`, as a subgroup of
`GL_n(𝔸)`. -/
def eisensteinRationalImage : Subgroup (Points F (r + 1)) :=
  (eisensteinParabolic F r).map (rationalPointHom F (r + 1))

theorem eisensteinRationalImage_le :
    eisensteinRationalImage F r ≤ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1)) := by
  rintro x ⟨g, -, rfl⟩
  exact rationalPoint_mem_rationalSubgroup F _ g

theorem rationalPoint_mem_eisensteinRationalImage {g : RationalGL F (r + 1)}
    (hg : g ∈ eisensteinParabolic F r) :
    rationalPoint F (r + 1) g ∈ eisensteinRationalImage F r :=
  ⟨g, hg, rfl⟩

theorem mirabolicRationalImage_le_eisensteinRationalImage :
    mirabolicRationalImage F r ≤ eisensteinRationalImage F r :=
  Subgroup.map_mono le_sup_left

theorem scalarPoint_mem_eisensteinRationalImage {b : Points F 1}
    (hb : b ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F 1)) :
    scalarPoint F r b ∈ eisensteinRationalImage F r := by
  obtain ⟨g, rfl⟩ := exists_rationalPoint_eq F 1 hb
  rw [scalarPoint_rationalPoint]
  refine rationalPoint_mem_eisensteinRationalImage F r (le_sup_right (a := GeneralLinear.mirabolic r F) ?_)
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨_, rfl⟩

/-- A rational scalar point lying in `P_n(F)` is the identity. -/
theorem eq_one_of_scalarPoint_mem_mirabolic {b : Points F 1}
    (hb : b ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F 1))
    (hbP : scalarPoint F r b ∈ mirabolicRationalImage F r) : b = 1 := by
  obtain ⟨g, rfl⟩ := exists_rationalPoint_eq F 1 hb
  rw [scalarPoint_rationalPoint, rationalPoint_mem_mirabolicRationalImage_iff] at hbP
  have h1 := hbP (Fin.last r)
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_eq, ite_true] at h1
  have hdet : Matrix.GeneralLinearGroup.det g = 1 := Units.ext h1
  apply ideleOf_injective F
  rw [ideleOf_rationalPoint, hdet, map_one, ideleOf_one]

/-- Every point of `P'_n(F)` is `diag(b, …, b) p⁻¹` for a rational `b ∈ GL_1(F)` and
`p ∈ P_n(F)`. -/
theorem exists_scalarPoint_mul_inv {l : Points F (r + 1)} (hl : l ∈ eisensteinRationalImage F r) :
    ∃ b ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F 1), ∃ p ∈ mirabolicRationalImage F r,
      scalarPoint F r b * p⁻¹ = l := by
  obtain ⟨g, hg, rfl⟩ := hl
  have hg' : g ∈ ((GeneralLinear.mirabolic r F ⊔
      Subgroup.center (RationalGL F (r + 1)) : Subgroup (RationalGL F (r + 1))) :
        Set (RationalGL F (r + 1))) := hg
  rw [Subgroup.mul_normal] at hg'
  obtain ⟨m, hm, c, hc, rfl⟩ := hg'
  have hc' := hc
  rw [SetLike.mem_coe, Matrix.GeneralLinearGroup.center_eq_range_scalar] at hc'
  obtain ⟨a, rfl⟩ := hc'
  refine ⟨rationalPoint F 1 (Matrix.GeneralLinearGroup.scalar (Fin 1) a),
    rationalPoint_mem_rationalSubgroup F 1 _, (rationalPoint F (r + 1) m)⁻¹,
    Subgroup.inv_mem _ ⟨m, hm, rfl⟩, ?_⟩
  rw [inv_inv, scalarPoint_commute, scalarPoint_rationalPoint, det_scalar_one,
    rationalPointHom_apply, rationalPoint_mul]

/-- The decomposition `l = diag(b, …, b) p⁻¹` is unique. -/
theorem scalarPoint_mul_inv_injective {b b' : Points F 1}
    (hb : b ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F 1))
    (hb' : b' ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F 1))
    {p p' : Points F (r + 1)} (hp : p ∈ mirabolicRationalImage F r)
    (hp' : p' ∈ mirabolicRationalImage F r)
    (h : scalarPoint F r b * p⁻¹ = scalarPoint F r b' * p'⁻¹) : b = b' ∧ p = p' := by
  have hb'' : b'⁻¹ * b ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F 1) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hb') hb
  have hmem : scalarPoint F r (b'⁻¹ * b) ∈ mirabolicRationalImage F r := by
    have : scalarPoint F r (b'⁻¹ * b) = p'⁻¹ * p := by
      rw [map_mul, map_inv]
      calc (scalarPoint F r b')⁻¹ * scalarPoint F r b
          = (scalarPoint F r b')⁻¹ * (scalarPoint F r b * p⁻¹) * p := by group
        _ = (scalarPoint F r b')⁻¹ * (scalarPoint F r b' * p'⁻¹) * p := by rw [h]
        _ = p'⁻¹ * p := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hp') hp
  have h1 := eq_one_of_scalarPoint_mem_mirabolic F r hb'' hmem
  have hbb : b = b' := by
    rw [← mul_inv_cancel_left b' b, h1, mul_one]
  subst hbb
  refine ⟨rfl, ?_⟩
  have := mul_left_cancel h
  exact inv_injective this

end Parabolic

end Langlands.Global.RankinSelbergGlobal.EqualUnfolding
