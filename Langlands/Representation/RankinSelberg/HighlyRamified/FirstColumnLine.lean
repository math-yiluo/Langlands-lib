import Langlands.Representation.Conductor.PrincipalCongruenceBasisProof

/-!
# The first-column line subgroup

`K⁰(I)` consists of the integral invertible matrices whose first column is
`(*, 0, …, 0)` modulo an ideal `I`. Over any commutative ring the matrices whose first
column is a multiple of `e_0` form a subgroup; `K⁰(I)` is its preimage under reduction,
included in the field group. It contains the principal congruence subgroup of `I`.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open Matrix Langlands.Conductor

universe uR uF

section Ring

variable (R : Type uR) [CommRing R] (n : ℕ)

/-- Invertible matrices whose first column is a multiple of `e_0`. -/
def firstColumnLine : Subgroup (GeneralLinearGroup (Fin (n + 1)) R) where
  carrier := {g | ∀ j : Fin (n + 1), j ≠ 0 → g j 0 = 0}
  one_mem' := by
    intro j hj
    simp [Matrix.one_apply_ne hj]
  mul_mem' := by
    intro g h hg hh j hj
    change ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) * h) j 0 = 0
    rw [Matrix.mul_apply, Finset.sum_eq_single 0]
    · rw [hg j hj, zero_mul]
    · intro l _ hl
      rw [hh l hl, mul_zero]
    · simp
  inv_mem' := by
    intro g hg j hj
    have hcol : ∀ i, ((g⁻¹ : GeneralLinearGroup (Fin (n + 1)) R) *
        (g : Matrix (Fin (n + 1)) (Fin (n + 1)) R)) i 0 =
        (g⁻¹ : GeneralLinearGroup (Fin (n + 1)) R) i 0 * g 0 0 := by
      intro i
      rw [Matrix.mul_apply, Finset.sum_eq_single 0]
      · intro l _ hl
        rw [hg l hl, mul_zero]
      · simp
    have hinv : ((g⁻¹ : GeneralLinearGroup (Fin (n + 1)) R) *
        (g : Matrix (Fin (n + 1)) (Fin (n + 1)) R)) = 1 := by
      rw [← GeneralLinearGroup.coe_mul, inv_mul_cancel, GeneralLinearGroup.coe_one]
    have h00 : (g⁻¹ : GeneralLinearGroup (Fin (n + 1)) R) 0 0 * g 0 0 = 1 := by
      rw [← hcol 0, hinv, Matrix.one_apply_eq]
    have hj0 : (g⁻¹ : GeneralLinearGroup (Fin (n + 1)) R) j 0 * g 0 0 = 0 := by
      rw [← hcol j, hinv, Matrix.one_apply_ne hj]
    have hunit : IsUnit (g 0 0) := IsUnit.of_mul_eq_one_right _ h00
    exact (hunit.mul_left_eq_zero).mp hj0

theorem mem_firstColumnLine (g : GeneralLinearGroup (Fin (n + 1)) R) :
    g ∈ firstColumnLine R n ↔ ∀ j : Fin (n + 1), j ≠ 0 → g j 0 = 0 := Iff.rfl

variable {R}

/-- Integral matrices whose first column is `(*, 0, …, 0)` modulo `I`. -/
def integralFirstColumn (I : Ideal R) : Subgroup (GeneralLinearGroup (Fin (n + 1)) R) :=
  (firstColumnLine (R ⧸ I) n).comap (GeneralLinearGroup.map (Ideal.Quotient.mk I))

theorem mem_integralFirstColumn (I : Ideal R) (g : GeneralLinearGroup (Fin (n + 1)) R) :
    g ∈ integralFirstColumn n I ↔ ∀ j : Fin (n + 1), j ≠ 0 → g j 0 ∈ I := by
  change (∀ j : Fin (n + 1), j ≠ 0 →
    (GeneralLinearGroup.map (Ideal.Quotient.mk I) g :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⧸ I)) j 0 = 0) ↔ _
  apply forall_congr'
  intro j
  apply imp_congr_right
  intro _
  rw [GeneralLinearGroup.map_apply, Ideal.Quotient.eq_zero_iff_mem]

theorem integralPrincipalCongruence_le_integralFirstColumn (I : Ideal R) :
    integralPrincipalCongruence n I ≤ integralFirstColumn n I := by
  intro g hg
  rw [mem_integralFirstColumn]
  intro j hj
  have := (mem_integralPrincipalCongruence n I g).1 hg j 0
  simpa [Matrix.one_apply_ne hj] using this

end Ring

section Field

variable {F : Type uF} [Field F] (O : Subring F) (n : ℕ)

/-- The first-column line subgroup of the field group at the ideal `I`. -/
def firstColumnCongruence (I : Ideal O) : Subgroup (GeneralLinearGroup (Fin (n + 1)) F) :=
  (integralFirstColumn n I).map (GeneralLinearGroup.map O.subtype)

theorem principalCongruenceSubgroup_le_firstColumnCongruence (I : Ideal O) :
    principalCongruenceSubgroup O n I ≤ firstColumnCongruence O n I :=
  Subgroup.map_mono (integralPrincipalCongruence_le_integralFirstColumn n I)

theorem firstColumnCongruence_le_integralSubgroup (I : Ideal O) :
    firstColumnCongruence O n I ≤ integralSubgroup O n := by
  rintro _ ⟨g, -, rfl⟩
  exact ⟨g, rfl⟩

/-- Entrywise membership: integral, with integral inverse, and first column
`(*, 0, …, 0)` modulo `I`. -/
theorem mem_firstColumnCongruence (I : Ideal O) (g : GeneralLinearGroup (Fin (n + 1)) F) :
    g ∈ firstColumnCongruence O n I ↔
      (∀ i j, g i j ∈ O) ∧ (∀ i j, g⁻¹ i j ∈ O) ∧
        ∀ j : Fin (n + 1), j ≠ 0 → ∃ x : O, x ∈ I ∧ (x : F) = g j 0 := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨fun i j => (h i j).property, fun i j => ?_, fun j hj => ?_⟩
    · rw [← map_inv]
      exact (h⁻¹ i j).property
    · exact ⟨h j 0, (mem_integralFirstColumn n I h).1 hh j hj, rfl⟩
  · rintro ⟨hg, hi, hcol⟩
    obtain ⟨h, rfl⟩ := (mem_integralSubgroup O n g).2 ⟨hg, hi⟩
    refine ⟨h, (mem_integralFirstColumn n I h).2 fun j hj => ?_, rfl⟩
    obtain ⟨x, hx, hxe⟩ := hcol j hj
    have : x = h j 0 := Subtype.val_injective hxe
    rw [← this]
    exact hx

end Field

section LocalField

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- `K⁰(f)`: the open first-column line subgroup at level `f`. -/
def firstColumnOpenSubgroup (n f : ℕ) : OpenSubgroup (GeneralLinearGroup (Fin (n + 1)) F) where
  toSubgroup := firstColumnCongruence (ValuativeRel.valuation F).integer n
    (IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ f)
  isOpen' := Subgroup.isOpen_mono
    (principalCongruenceSubgroup_le_firstColumnCongruence _ n _)
    (principalLevelOpenSubgroup F n f).isOpen

theorem isCompact_firstColumnOpenSubgroup (n f : ℕ) :
    IsCompact (firstColumnOpenSubgroup F n f : Set (GeneralLinearGroup (Fin (n + 1)) F)) := by
  have hc := isCompact_levelOpenSubgroup F n 0
  have hle : (firstColumnOpenSubgroup F n f : Set (GeneralLinearGroup (Fin (n + 1)) F)) ⊆
      (levelOpenSubgroup F n 0 : Set (GeneralLinearGroup (Fin (n + 1)) F)) := by
    intro g hg
    change g ∈ levelSubgroup F n 0
    rw [levelSubgroup_zero]
    exact firstColumnCongruence_le_integralSubgroup _ n _ hg
  exact hc.of_isClosed_subset (firstColumnOpenSubgroup F n f).isClosed hle

end LocalField

end Langlands.RankinSelberg.HighlyRamified
