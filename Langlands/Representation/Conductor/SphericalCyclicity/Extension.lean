import Langlands.Representation.Conductor.SphericalCyclicity.Parahoric

/-!
# Extension by zero from the big cell

For `z : Fin (n + 2) → ℂˣ` let `z' i = z (i + 1)`.  A function `ψ` in the principal series
of rank `n + 1` with parameters `z'` is extended to a function on `GL_(n+2)(F)` that is
supported on the big cell: on the cell its value at `x` is
`z₀ ^ e * √q ^ (-(n + 1) e + d) * ψ (D)`, where `D` is the lower-right block of `x`,
`d = ord det D` and `e = ord det x - d`.  This file proves that the extension lies in the
principal series of rank `n + 2` with parameters `z`, and records how it transforms under
right multiplication by lower unipotent and block-diagonal matrices.
-/

noncomputable section

namespace Langlands.Conductor.SphericalCyclicity

open Matrix Langlands.GeneralLinear Langlands.Conductor
open Langlands.Conductor.UnramifiedPrincipalSeries Langlands.Induction
open scoped BigOperators

universe uF

variable {F : Type uF} [Field F] [ValuativeRel F]

set_option quotPrecheck false in
local notation "𝒱" => ValuativeRel.valuation F
set_option quotPrecheck false in
local notation "𝒪" => (ValuativeRel.valuation F).integer

variable {ϖ : Fˣ} (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ)

variable {n : ℕ}

/-! ### The lower-right block of an upper-triangular matrix -/

omit [ValuativeRel F] in
theorem colT_borel (b : Borel (F := F) (n + 1)) : colT b.val.val = 0 := by
  ext i
  have hb : (b.val : Matrix (Fin (n + 2)) (Fin (n + 2)) F).IsUpperTriangular := b.property
  exact hb (Fin.succ_pos i)

omit [ValuativeRel F] in
theorem isUnit_det_low_borel (b : Borel (F := F) (n + 1)) : IsUnit (low b.val.val).det :=
  (isUnit_of_colT_eq_zero (colT_borel b)).1

/-- The lower-right block of an upper-triangular matrix, in the smaller Borel. -/
def lowBorel (b : Borel (F := F) (n + 1)) : Borel (F := F) n :=
  ⟨lowGL b.val, by
    change ((lowGL b.val : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F).IsUpperTriangular
    rw [lowGL_val (isUnit_det_low_borel b)]
    intro i j hij
    have hb : (b.val : Matrix (Fin (n + 2)) (Fin (n + 2)) F).IsUpperTriangular := b.property
    exact hb (Fin.succ_lt_succ_iff.2 hij)⟩

omit [ValuativeRel F] in
theorem lowBorel_val (b : Borel (F := F) (n + 1)) :
    ((lowBorel b).val : Matrix (Fin (n + 1)) (Fin (n + 1)) F) = low b.val.val :=
  lowGL_val (isUnit_det_low_borel b)

omit [ValuativeRel F] in
theorem lowBorel_coe (b : Borel (F := F) (n + 1)) : (lowBorel b).val = lowGL b.val := rfl

omit [ValuativeRel F] in
theorem diagonalUnit_lowBorel (b : Borel (F := F) (n + 1)) (i : Fin (n + 1)) :
    diagonalUnit n i (lowBorel b) = diagonalUnit (n + 1) i.succ b := by
  apply Units.ext
  rw [diagonalUnit_val, diagonalUnit_val, lowBorel_val]
  rfl

theorem ord_prod {ι : Type*} (s : Finset ι) (f : ι → Fˣ) :
    ord hϖ (∏ i ∈ s, f i) = ∑ i ∈ s, ord hϖ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ord_mul, ih]

theorem ordDet_borel {m : ℕ} (b : Borel (F := F) m) :
    ordDet hϖ b.val = ∑ i, ord hϖ (diagonalUnit m i b) := by
  have h : Matrix.GeneralLinearGroup.det b.val = ∏ i, diagonalUnit m i b := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_prod,
      Matrix.det_of_isUpperTriangular b.property]
    rfl
  rw [ordDet, h, ord_prod]

theorem ord_headUnit_borel (b : Borel (F := F) (n + 1)) (hp : colT b.val.val = 0) :
    ord hϖ (headUnit hp) = ord hϖ (diagonalUnit (n + 1) 0 b) := rfl

/-! ### Splitting the normalized character -/

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- The parameters of the smaller principal series. -/
def tailParam (z : Fin (n + 2) → ℂˣ) : Fin (n + 1) → ℂˣ := fun i => z i.succ

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem modulus_exponent_split (o : Fin (n + 2) → ℤ) :
    -∑ i : Fin (n + 2), (((n + 1 : ℕ) : ℤ) - 2 * ((i : ℕ) : ℤ)) * o i =
      (-((n : ℤ) + 1) * o 0 + ∑ j : Fin (n + 1), o j.succ) +
        -∑ j : Fin (n + 1), ((n : ℤ) - 2 * ((j : ℕ) : ℤ)) * o j.succ := by
  rw [Fin.sum_univ_succ]
  have h : ∀ j : Fin (n + 1), (((n + 1 : ℕ) : ℤ) - 2 * (((j.succ : Fin (n + 2)) : ℕ) : ℤ)) *
      o j.succ = ((n : ℤ) - 2 * ((j : ℕ) : ℤ)) * o j.succ - o j.succ := by
    intro j
    rw [Fin.val_succ]
    push_cast
    ring
  simp only [h, Finset.sum_sub_distrib, Fin.val_zero]
  push_cast
  ring

theorem halfModulusCharacter_split {q : ℕ} (hq : IsResidueCardinality (F := F) q)
    (b : Borel (F := F) (n + 1)) :
    halfModulusCharacter hϖ (n + 1) hq b =
      sqrtResidueUnit hq ^ (-((n : ℤ) + 1) * ord hϖ (diagonalUnit (n + 1) 0 b) +
        ordDet hϖ (lowBorel b).val) * halfModulusCharacter hϖ n hq (lowBorel b) := by
  simp only [halfModulusCharacter, modulusExponent, MonoidHom.comp_apply, MonoidHom.coe_mk,
    OneHom.coe_mk, zpowersHom_apply, toAdd_ofAdd]
  rw [← _root_.zpow_add, ordDet_borel]
  congr 1
  simp only [diagonalUnit_lowBorel]
  exact modulus_exponent_split (fun i => ord hϖ (diagonalUnit (n + 1) i b))

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem inducingCharacter_split (z : Fin (n + 2) → ℂˣ) (b : Borel (F := F) (n + 1)) :
    inducingCharacter hϖ (n + 1) z b =
      z 0 ^ ord hϖ (diagonalUnit (n + 1) 0 b) *
        inducingCharacter hϖ n (tailParam z) (lowBorel b) := by
  rw [inducingCharacter_apply, inducingCharacter_apply, Fin.prod_univ_succ]
  simp only [diagonalUnit_lowBorel, tailParam]

/-- The normalized character of rank `n + 2` in terms of the head entry and the
normalized character of rank `n + 1` of the lower-right block. -/
theorem normalizedCharacter_split {q : ℕ} (hq : IsResidueCardinality (F := F) q)
    (z : Fin (n + 2) → ℂˣ) (b : Borel (F := F) (n + 1)) :
    normalizedCharacter hϖ (n + 1) hq z b =
      z 0 ^ ord hϖ (diagonalUnit (n + 1) 0 b) *
        sqrtResidueUnit hq ^ (-((n : ℤ) + 1) * ord hϖ (diagonalUnit (n + 1) 0 b) +
          ordDet hϖ (lowBorel b).val) *
        normalizedCharacter hϖ n hq (tailParam z) (lowBorel b) := by
  simp only [normalizedCharacter, MonoidHom.mul_apply]
  rw [halfModulusCharacter_split, inducingCharacter_split]
  ac_rfl

/-! ### Values of principal-series functions -/

theorem value_borel_mul {m q : ℕ} {hq : IsResidueCardinality (F := F) q}
    {z : Fin (m + 1) → ℂˣ} (f : PrincipalSeries hϖ m hq z) (b : Borel (F := F) m)
    (g : GL (Fin (m + 1)) F) :
    value hϖ m f (b.val * g) = (normalizedCharacter hϖ m hq z b : ℂ) * value hϖ m f g :=
  f.val.property b g

/-- Every principal-series function is right invariant under a principal congruence
subgroup of positive level. -/
theorem exists_level {m q : ℕ} {hq : IsResidueCardinality (F := F) q}
    {z : Fin (m + 1) → ℂˣ} (f : PrincipalSeries hϖ m hq z) :
    ∃ a : ℕ, 0 < a ∧ ∀ h ∈ principalLevelSubgroup F m a, ∀ g,
      value hϖ m f (g * h) = value hϖ m f g := by
  obtain ⟨K, hK⟩ := f.property
  obtain ⟨a, ha, hsub⟩ := exists_pos_principalLevelOpenSubgroup_subset F m K.mem_nhds_one
  refine ⟨a, ha, fun h hh g => ?_⟩
  have := hK ⟨h, hsub hh⟩
  exact congrArg (fun f => f.val g) this

/-! ### Cell functions -/

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem lowGL_congr {x x' : GL (Fin (n + 2)) F} (h : low x.val = low x'.val) :
    lowGL x = lowGL x' := by
  by_cases hu : IsUnit (low x.val).det
  · have hu' : IsUnit (low x'.val).det := h ▸ hu
    apply Units.ext
    rw [lowGL_val hu, lowGL_val hu', h]
  · have hu' : ¬IsUnit (low x'.val).det := h ▸ hu
    rw [lowGL, dif_neg hu, lowGL, dif_neg hu']

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem lowGL_mul_lowerUnip (x : GL (Fin (n + 2)) F) (y : Fin (n + 1) → F) :
    lowGL (x * lowerUnip y) = lowGL x :=
  lowGL_congr (by rw [Units.val_mul, low_mul_lowerUnip])

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem isUnit_det_low_mul_lowerUnip (x : GL (Fin (n + 2)) F) (y : Fin (n + 1) → F) :
    IsUnit (low (x * lowerUnip y).val).det ↔ IsUnit (low x.val).det := by
  rw [Units.val_mul, low_mul_lowerUnip]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem cellVec_mul_lowerUnip {x : GL (Fin (n + 2)) F} (hx : IsUnit (low x.val).det)
    (y : Fin (n + 1) → F) : cellVec (x * lowerUnip y) = cellVec x + y := by
  rw [cellVec, Units.val_mul, low_mul_lowerUnip, colT_mul, lowerUnip_val]
  simp only [blk_zero_zero, one_smul, colT_blk]
  rw [mulVec_add, mulVec_mulVec, Matrix.nonsing_inv_mul _ hx, one_mulVec, cellVec]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem ordDet_mul_lowerUnip (x : GL (Fin (n + 2)) F) (y : Fin (n + 1) → F) :
    ordDet hϖ (x * lowerUnip y) = ordDet hϖ x := by
  have h : Matrix.GeneralLinearGroup.det (lowerUnip y : GL (Fin (n + 2)) F) = 1 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, det_lowerUnip, Units.val_one]
  have h0 : ordDet hϖ (lowerUnip y : GL (Fin (n + 2)) F) = 0 := by
    rw [ordDet, h, ord_one]
  rw [ordDet_mul, h0, add_zero]

/-- The difference `ord det x - ord det D` for the lower-right block `D` of `x`. -/
def headOrd (x : GL (Fin (n + 2)) F) : ℤ := ordDet hϖ x - ordDet hϖ (lowGL x)

/-- The scalar factor of the extension at `x`. -/
def cellScalar {q : ℕ} (hq : IsResidueCardinality (F := F) q) (z : Fin (n + 2) → ℂˣ)
    (x : GL (Fin (n + 2)) F) : ℂˣ :=
  z 0 ^ headOrd hϖ x *
    sqrtResidueUnit hq ^ (-((n : ℤ) + 1) * headOrd hϖ x + ordDet hϖ (lowGL x))

theorem cellScalar_mul_lowerUnip {q : ℕ} (hq : IsResidueCardinality (F := F) q)
    (z : Fin (n + 2) → ℂˣ) (x : GL (Fin (n + 2)) F) (y : Fin (n + 1) → F) :
    cellScalar hϖ hq z (x * lowerUnip y) = cellScalar hϖ hq z x := by
  simp only [cellScalar, headOrd, ordDet_mul_lowerUnip, lowGL_mul_lowerUnip]

/-- Vectors all of whose coordinates lie in the maximal ideal. -/
def IsSmall {m : ℕ} (v : Fin m → F) : Prop := ∀ i, 𝒱 (v i) < 1

open Classical in
/-- The function on `GL_(n+2)(F)` supported on the matrices `x` whose lower-right block
`D` is invertible and for which `D⁻¹ c` satisfies `P`, with value
`cellScalar x * φ D` there. -/
def cellFun {q : ℕ} (hq : IsResidueCardinality (F := F) q) (z : Fin (n + 2) → ℂˣ)
    (P : (Fin (n + 1) → F) → Prop) (φ : GL (Fin (n + 1)) F → ℂ) (x : GL (Fin (n + 2)) F) : ℂ :=
  if IsUnit (low x.val).det ∧ P (cellVec x) then (cellScalar hϖ hq z x : ℂ) * φ (lowGL x) else 0

theorem cellFun_of {q : ℕ} {hq : IsResidueCardinality (F := F) q} {z : Fin (n + 2) → ℂˣ}
    {P : (Fin (n + 1) → F) → Prop} (φ : GL (Fin (n + 1)) F → ℂ) {x : GL (Fin (n + 2)) F}
    (h : IsUnit (low x.val).det ∧ P (cellVec x)) :
    cellFun hϖ hq z P φ x = (cellScalar hϖ hq z x : ℂ) * φ (lowGL x) := by
  unfold cellFun
  exact if_pos h

theorem cellFun_of_not {q : ℕ} {hq : IsResidueCardinality (F := F) q} {z : Fin (n + 2) → ℂˣ}
    {P : (Fin (n + 1) → F) → Prop} (φ : GL (Fin (n + 1)) F → ℂ) {x : GL (Fin (n + 2)) F}
    (h : ¬(IsUnit (low x.val).det ∧ P (cellVec x))) : cellFun hϖ hq z P φ x = 0 := by
  unfold cellFun
  exact if_neg h

/-- A cell function is determined by its values on the matrices satisfying its
condition, where it is given by the scalar factor times `φ` of the lower-right block. -/
theorem cellFun_eq_of_iff {q : ℕ} {hq : IsResidueCardinality (F := F) q}
    {z : Fin (n + 2) → ℂˣ} {P P' : (Fin (n + 1) → F) → Prop} {φ φ' : GL (Fin (n + 1)) F → ℂ}
    {x x' : GL (Fin (n + 2)) F} (c : ℂ)
    (hiff : IsUnit (low x'.val).det ∧ P' (cellVec x') ↔ IsUnit (low x.val).det ∧ P (cellVec x))
    (hval : IsUnit (low x.val).det ∧ P (cellVec x) →
      (cellScalar hϖ hq z x' : ℂ) * φ' (lowGL x') = c * ((cellScalar hϖ hq z x : ℂ) * φ (lowGL x))) :
    cellFun hϖ hq z P' φ' x' = c * cellFun hϖ hq z P φ x := by
  by_cases h : IsUnit (low x.val).det ∧ P (cellVec x)
  · rw [cellFun_of hϖ φ' (hiff.2 h), cellFun_of hϖ φ h, hval h]
  · rw [cellFun_of_not hϖ φ' (fun h' => h (hiff.1 h')), cellFun_of_not hϖ φ h, mul_zero]

theorem cellFun_mul_lowerUnip {q : ℕ} (hq : IsResidueCardinality (F := F) q)
    (z : Fin (n + 2) → ℂˣ) (P : (Fin (n + 1) → F) → Prop) (φ : GL (Fin (n + 1)) F → ℂ)
    (x : GL (Fin (n + 2)) F) (y : Fin (n + 1) → F) :
    cellFun hϖ hq z P φ (x * lowerUnip y) = cellFun hϖ hq z (fun v => P (v + y)) φ x := by
  rw [← one_mul (cellFun hϖ hq z (fun v => P (v + y)) φ x)]
  apply cellFun_eq_of_iff
  · rw [isUnit_det_low_mul_lowerUnip]
    constructor
    · rintro ⟨hx, hP⟩
      exact ⟨hx, by rwa [cellVec_mul_lowerUnip hx] at hP⟩
    · rintro ⟨hx, hP⟩
      exact ⟨hx, by rwa [cellVec_mul_lowerUnip hx]⟩
  · intro _
    rw [cellScalar_mul_lowerUnip, lowGL_mul_lowerUnip, one_mul]

/-- How the scalar factor changes when the head order and the lower-right determinant
order are shifted. -/
theorem cellScalar_eq_of {q : ℕ} (hq : IsResidueCardinality (F := F) q)
    (z : Fin (n + 2) → ℂˣ) {x x' : GL (Fin (n + 2)) F} {o d : ℤ}
    (ho : headOrd hϖ x' = headOrd hϖ x + o)
    (hd : ordDet hϖ (lowGL x') = ordDet hϖ (lowGL x) + d) :
    cellScalar hϖ hq z x' =
      z 0 ^ o * sqrtResidueUnit hq ^ (-((n : ℤ) + 1) * o + d) * cellScalar hϖ hq z x := by
  unfold cellScalar
  rw [ho, hd]
  have h1 : -((n : ℤ) + 1) * (headOrd hϖ x + o) + (ordDet hϖ (lowGL x) + d) =
      (-((n : ℤ) + 1) * o + d) + (-((n : ℤ) + 1) * headOrd hϖ x + ordDet hϖ (lowGL x)) := by
    ring
  rw [h1, _root_.zpow_add (z 0) (headOrd hϖ x) o,
    _root_.zpow_add (sqrtResidueUnit hq) (-((n : ℤ) + 1) * o + d),
    mul_comm (z 0 ^ headOrd hϖ x) (z 0 ^ o), mul_mul_mul_comm]

/-! ### Right multiplication by block-diagonal matrices -/

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem low_mul_blockDiag (X : Matrix (Fin (n + 2)) (Fin (n + 2)) F) (α : Fˣ)
    (h : GL (Fin (n + 1)) F) : low (X * (blockDiag α h).val) = low X * h.val := by
  rw [low_mul, blockDiag_val]
  simp

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem colT_mul_blockDiag (X : Matrix (Fin (n + 2)) (Fin (n + 2)) F) (α : Fˣ)
    (h : GL (Fin (n + 1)) F) : colT (X * (blockDiag α h).val) = (α : F) • colT X := by
  rw [colT_mul, blockDiag_val]
  simp

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem isUnit_det_low_mul_blockDiag (x : GL (Fin (n + 2)) F) (α : Fˣ)
    (h : GL (Fin (n + 1)) F) :
    IsUnit (low (x * blockDiag α h).val).det ↔ IsUnit (low x.val).det := by
  rw [Units.val_mul, low_mul_blockDiag, det_mul, IsUnit.mul_iff]
  exact ⟨fun hh => hh.1, fun hh => ⟨hh, (Matrix.isUnit_iff_isUnit_det _).1 h.isUnit⟩⟩

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem cellVec_mul_blockDiag (x : GL (Fin (n + 2)) F) (α : Fˣ) (h : GL (Fin (n + 1)) F) :
    cellVec (x * blockDiag α h) = (α : F) • ((h⁻¹ : GL (Fin (n + 1)) F).val *ᵥ cellVec x) := by
  rw [cellVec, cellVec, Units.val_mul, low_mul_blockDiag, colT_mul_blockDiag,
    Matrix.mul_inv_rev, Matrix.coe_units_inv, mulVec_smul, mulVec_mulVec]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem lowGL_mul_blockDiag {x : GL (Fin (n + 2)) F} (hx : IsUnit (low x.val).det) (α : Fˣ)
    (h : GL (Fin (n + 1)) F) : lowGL (x * blockDiag α h) = lowGL x * h := by
  apply Units.ext
  rw [lowGL_val ((isUnit_det_low_mul_blockDiag x α h).2 hx), Units.val_mul,
    low_mul_blockDiag, Units.val_mul, lowGL_val hx]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem ordDet_blockDiag (α : Fˣ) (h : GL (Fin (n + 1)) F) :
    ordDet hϖ (blockDiag α h) = ord hϖ α + ordDet hϖ h := by
  have e : Matrix.GeneralLinearGroup.det (blockDiag α h) =
      α * Matrix.GeneralLinearGroup.det h := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, blockDiag_val, det_blk_zero, Units.val_mul,
      Matrix.GeneralLinearGroup.val_det_apply]
  rw [ordDet, e, ord_mul]
  rfl

theorem cellFun_mul_blockDiag {q : ℕ} (hq : IsResidueCardinality (F := F) q)
    (z : Fin (n + 2) → ℂˣ) (P : (Fin (n + 1) → F) → Prop) (φ : GL (Fin (n + 1)) F → ℂ)
    (x : GL (Fin (n + 2)) F) (α : Fˣ) (h : GL (Fin (n + 1)) F) :
    cellFun hϖ hq z P φ (x * blockDiag α h) =
      ((z 0 ^ ord hϖ α * sqrtResidueUnit hq ^ (-((n : ℤ) + 1) * ord hϖ α + ordDet hϖ h) : ℂˣ) :
        ℂ) *
        cellFun hϖ hq z (fun v => P ((α : F) • ((h⁻¹ : GL (Fin (n + 1)) F).val *ᵥ v)))
          (fun g => φ (g * h)) x := by
  apply cellFun_eq_of_iff
  · rw [isUnit_det_low_mul_blockDiag, cellVec_mul_blockDiag]
  · rintro ⟨hx, _⟩
    have hl := lowGL_mul_blockDiag hx α h
    have hs : cellScalar hϖ hq z (x * blockDiag α h) = z 0 ^ ord hϖ α *
        sqrtResidueUnit hq ^ (-((n : ℤ) + 1) * ord hϖ α + ordDet hϖ h) *
          cellScalar hϖ hq z x := by
      apply cellScalar_eq_of
      · rw [headOrd, headOrd, hl, ordDet_mul, ordDet_mul, ordDet_blockDiag]
        ring
      · rw [hl, ordDet_mul]
    rw [hs, hl]
    push_cast
    ring

/-! ### Left multiplication by the Borel subgroup -/

theorem cellFun_borel_mul {q : ℕ} (hq : IsResidueCardinality (F := F) q)
    (z : Fin (n + 2) → ℂˣ) (P : (Fin (n + 1) → F) → Prop) (φ : GL (Fin (n + 1)) F → ℂ)
    (hφ : ∀ (b' : Borel (F := F) n) (g : GL (Fin (n + 1)) F),
      φ (b'.val * g) = (normalizedCharacter hϖ n hq (tailParam z) b' : ℂ) * φ g)
    (b : Borel (F := F) (n + 1)) (x : GL (Fin (n + 2)) F) :
    cellFun hϖ hq z P φ (b.val * x) =
      (normalizedCharacter hϖ (n + 1) hq z b : ℂ) * cellFun hϖ hq z P φ x := by
  apply cellFun_eq_of_iff
  · rw [isUnit_det_low_mul_iff (colT_borel b), cellVec_mul_of_colT_eq_zero (colT_borel b)]
  · rintro ⟨hx, _⟩
    have hl : lowGL (b.val * x) = (lowBorel b).val * lowGL x := by
      rw [lowBorel_coe, lowGL_mul_of_colT_eq_zero (colT_borel b) hx]
    have hs : cellScalar hϖ hq z (b.val * x) = z 0 ^ ord hϖ (diagonalUnit (n + 1) 0 b) *
        sqrtResidueUnit hq ^ (-((n : ℤ) + 1) * ord hϖ (diagonalUnit (n + 1) 0 b) +
          ordDet hϖ (lowBorel b).val) * cellScalar hϖ hq z x := by
      apply cellScalar_eq_of
      · rw [headOrd, headOrd, hl, ordDet_mul, ordDet_mul,
          ordDet_of_colT_eq_zero hϖ (colT_borel b), ord_headUnit_borel, lowBorel_coe]
        ring
      · rw [hl, ordDet_mul]
        ring
    rw [hs, hl, hφ, normalizedCharacter_split]
    push_cast
    ring

/-! ### Right multiplication by the parahoric subgroup -/

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem isSmall_iff {m : ℕ} (v : Fin m → F) : IsSmall v ↔ ∀ i, 𝒱 (v i) < 1 := Iff.rfl

open Classical in
theorem cellFun_isSmall {q : ℕ} (hq : IsResidueCardinality (F := F) q)
    (z : Fin (n + 2) → ℂˣ) (φ : GL (Fin (n + 1)) F → ℂ) (x : GL (Fin (n + 2)) F) :
    cellFun hϖ hq z IsSmall φ x =
      if InCell x then (cellScalar hϖ hq z x : ℂ) * φ (lowGL x) else 0 := by
  unfold cellFun
  exact if_congr Iff.rfl rfl rfl

open Classical in
theorem cellFun_mul_parahoric {q : ℕ} (hq : IsResidueCardinality (F := F) q)
    (z : Fin (n + 2) → ℂˣ) (φ : GL (Fin (n + 1)) F → ℂ) (x : GL (Fin (n + 2)) F)
    {k : GL (Fin (n + 2)) F} (hk : k ∈ parahoric ϖ) :
    cellFun hϖ hq z IsSmall φ (x * k) =
      if InCell x then
        (cellScalar hϖ hq z x : ℂ) * φ (lowGL x * lowGL (lowerUnip (cellVec x) * k))
      else 0 := by
  rw [cellFun_isSmall]
  by_cases hx : InCell x
  · obtain ⟨hxk, hu, hl⟩ := cell_mul_parahoric hϖ hx hk
    have hkK := ((mem_parahoric_iff hϖ k).1 hk).1
    have hs : cellScalar hϖ hq z (x * k) = cellScalar hϖ hq z x := by
      have := cellScalar_eq_of hϖ hq z (x := x) (x' := x * k) (o := 0) (d := 0) ?_ ?_
      · simpa using this
      · rw [headOrd, headOrd, hl, ordDet_mul, ordDet_mul, ordDet_eq_zero_of_integral hϖ hkK,
          ordDet_eq_zero_of_integral hϖ (lowGL_mem_integral_of_parahoric hϖ hu)]
        ring
      · rw [hl, ordDet_mul, ordDet_eq_zero_of_integral hϖ (lowGL_mem_integral_of_parahoric hϖ hu)]
    rw [if_pos hxk, if_pos hx, hs, hl]
  · rw [if_neg (fun h => hx (inCell_of_mul_parahoric hϖ h hk)), if_neg hx]

/-! ### The extension map -/

/-- The extension by zero of a principal-series function of rank `n + 1`. -/
def extFun {q : ℕ} {hq : IsResidueCardinality (F := F) q} {z : Fin (n + 2) → ℂˣ}
    (ψ : PrincipalSeries hϖ n hq (tailParam z)) (x : GL (Fin (n + 2)) F) : ℂ :=
  cellFun hϖ hq z IsSmall (value hϖ n ψ) x

open Classical in
theorem extFun_apply {q : ℕ} {hq : IsResidueCardinality (F := F) q} {z : Fin (n + 2) → ℂˣ}
    (ψ : PrincipalSeries hϖ n hq (tailParam z)) (x : GL (Fin (n + 2)) F) :
    extFun hϖ ψ x =
      if InCell x then (cellScalar hϖ hq z x : ℂ) * value hϖ n ψ (lowGL x) else 0 :=
  cellFun_isSmall hϖ hq z _ x

theorem extFun_covariance {q : ℕ} {hq : IsResidueCardinality (F := F) q}
    {z : Fin (n + 2) → ℂˣ} (ψ : PrincipalSeries hϖ n hq (tailParam z))
    (b : Borel (F := F) (n + 1)) (x : GL (Fin (n + 2)) F) :
    extFun hϖ ψ (b.val * x) = (normalizedCharacter hϖ (n + 1) hq z b : ℂ) * extFun hϖ ψ x :=
  cellFun_borel_mul hϖ hq z _ _ (value_borel_mul hϖ ψ) b x

theorem extFun_mul_level {q : ℕ} {hq : IsResidueCardinality (F := F) q}
    {z : Fin (n + 2) → ℂˣ} (ψ : PrincipalSeries hϖ n hq (tailParam z)) {a : ℕ} (ha : 0 < a)
    (hψ : ∀ h ∈ principalLevelSubgroup F n a, ∀ g, value hϖ n ψ (g * h) = value hϖ n ψ g)
    {k : GL (Fin (n + 2)) F} (hk : k ∈ principalLevelSubgroup F (n + 1) a)
    (x : GL (Fin (n + 2)) F) : extFun hϖ ψ (x * k) = extFun hϖ ψ x := by
  rw [extFun, cellFun_mul_parahoric hϖ hq z _ x (mem_parahoric_of_principalLevel hϖ ha hk),
    extFun_apply]
  by_cases hx : InCell x
  · rw [if_pos hx, if_pos hx, hψ _ (lowGL_lowerUnip_mul_mem_principalLevel hϖ ha hx.2 hk)]
  · rw [if_neg hx, if_neg hx]

/-- A chosen positive level fixing a principal-series function. -/
def level {m q : ℕ} {hq : IsResidueCardinality (F := F) q} {z : Fin (m + 1) → ℂˣ}
    (f : PrincipalSeries hϖ m hq z) : ℕ :=
  (exists_level hϖ f).choose

theorem level_pos {m q : ℕ} {hq : IsResidueCardinality (F := F) q} {z : Fin (m + 1) → ℂˣ}
    (f : PrincipalSeries hϖ m hq z) : 0 < level hϖ f :=
  (exists_level hϖ f).choose_spec.1

theorem level_spec {m q : ℕ} {hq : IsResidueCardinality (F := F) q} {z : Fin (m + 1) → ℂˣ}
    (f : PrincipalSeries hϖ m hq z) :
    ∀ h ∈ principalLevelSubgroup F m (level hϖ f), ∀ g,
      value hϖ m f (g * h) = value hϖ m f g :=
  (exists_level hϖ f).choose_spec.2

theorem value_add {m q : ℕ} {hq : IsResidueCardinality (F := F) q} {z : Fin (m + 1) → ℂˣ}
    (f g : PrincipalSeries hϖ m hq z) (x : GL (Fin (m + 1)) F) :
    value hϖ m (f + g) x = value hϖ m f x + value hϖ m g x := rfl

theorem value_smul {m q : ℕ} {hq : IsResidueCardinality (F := F) q} {z : Fin (m + 1) → ℂˣ}
    (c : ℂ) (f : PrincipalSeries hϖ m hq z) (x : GL (Fin (m + 1)) F) :
    value hϖ m (c • f) x = c * value hϖ m f x := rfl

/-- The extension-by-zero map from the principal series of rank `n + 1` with parameters
`z ∘ succ` to the principal series of rank `n + 2` with parameters `z`. -/
def extend {q : ℕ} (hq : IsResidueCardinality (F := F) q) (z : Fin (n + 2) → ℂˣ) :
    PrincipalSeries hϖ n hq (tailParam z) →ₗ[ℂ] PrincipalSeries hϖ (n + 1) hq z where
  toFun ψ := smoothFunctionOf _ _ (extFun hϖ ψ) (fun b x => extFun_covariance hϖ ψ b x)
    (principalLevelOpenSubgroup F (n + 1) (level hϖ ψ))
    (fun k x => extFun_mul_level hϖ ψ (level_pos hϖ ψ) (level_spec hϖ ψ) k.property x)
  map_add' ψ₁ ψ₂ := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change extFun hϖ (ψ₁ + ψ₂) x = extFun hϖ ψ₁ x + extFun hϖ ψ₂ x
    rw [extFun_apply, extFun_apply, extFun_apply, value_add]
    split_ifs
    · ring
    · simp
  map_smul' c ψ := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change extFun hϖ (c • ψ) x = c * extFun hϖ ψ x
    rw [extFun_apply, extFun_apply, value_smul]
    split_ifs
    · ring
    · simp

theorem extend_value {q : ℕ} (hq : IsResidueCardinality (F := F) q) (z : Fin (n + 2) → ℂˣ)
    (ψ : PrincipalSeries hϖ n hq (tailParam z)) (x : GL (Fin (n + 2)) F) :
    value hϖ (n + 1) (extend hϖ hq z ψ) x = extFun hϖ ψ x := rfl

end Langlands.Conductor.SphericalCyclicity
