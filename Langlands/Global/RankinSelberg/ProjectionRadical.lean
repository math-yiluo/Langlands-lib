import Langlands.Global.RankinSelberg.ProjectionColumns

/-! # The radicals `Y_(r+1,j)` of the projection and their column complements -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Opposite Topology
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
  PrimitiveAdelicHeight

section Matrix

variable {A : Type*} [CommRing A] {r : ℕ}

/-- The order of the projection weights: `e_j(a) ≤ e_j(b)` iff `b ≤ j` or `b ≤ a`. -/
theorem projectionWeight_le_iff (j : ℕ) (a b : Fin (r + 1)) :
    projectionWeight (r + 1) j a ≤ projectionWeight (r + 1) j b ↔
      (b : ℕ) ≤ j ∨ (b : ℕ) ≤ a := by
  simp only [projectionWeight]
  omega

/-- The projection weights coarsen as the initial block grows. -/
theorem projectionWeight_mono (j : ℕ) (a b : Fin (r + 1))
    (h : projectionWeight (r + 1) j a ≤ projectionWeight (r + 1) j b) :
    projectionWeight (r + 1) (j + 1) a ≤ projectionWeight (r + 1) (j + 1) b := by
  rw [projectionWeight_le_iff] at h ⊢
  omega

/-- `Y_(r+1,j)` consists of the upper unitriangular matrices whose first `j + 1` columns are
those of the identity. -/
theorem mem_projectionSubgroup_iff (j : ℕ) (g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
    g ∈ blockUnipotentSubgroup A (projectionWeight (r + 1) j) ↔
      IsUnitriangular (g : Matrix (Fin (r + 1)) (Fin (r + 1)) A) ∧
        ∀ a b : Fin (r + 1), (b : ℕ) ≤ j →
          (g : Matrix (Fin (r + 1)) (Fin (r + 1)) A) a b = (1 : Matrix _ _ A) a b := by
  rw [mem_blockUnipotentSubgroup]
  constructor
  · intro h
    refine ⟨⟨fun a b hab => ?_, fun a => ?_⟩, fun a b hb => h a b
      ((projectionWeight_le_iff j a b).mpr (Or.inl hb))⟩
    · have hab' : (b : ℕ) < a := hab
      have hne : a ≠ b := fun h => by subst h; omega
      rw [h a b ((projectionWeight_le_iff j a b).mpr (Or.inr hab'.le)),
        Matrix.one_apply_ne hne]
    · rw [h a a le_rfl, Matrix.one_apply_eq]
  · rintro ⟨hu, hcol⟩ a b hab
    rcases (projectionWeight_le_iff j a b).mp hab with hb | hb
    · exact hcol a b hb
    · rcases (Fin.le_iff_val_le_val.mpr hb).lt_or_eq with hlt | heq
      · have hne : a ≠ b := fun h => by subst h; exact lt_irrefl _ hlt
        rw [hu.1 hlt, Matrix.one_apply_ne hne]
      · subst heq
        rw [hu.2 b, Matrix.one_apply_eq]

/-- The block Levi part of `Y_(r+1,j)` relative to `Y_(r+1,j+1)` is the column `j + 1` above
the diagonal. -/
theorem mem_columnSubgroup_iff (j : ℕ) (g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
    g ∈ blockUnipotentSubgroup A (projectionWeight (r + 1) j) ⊓
        blockLeviSubgroup A (projectionWeight (r + 1) (j + 1)) ↔
      ∀ a b : Fin (r + 1), ¬((b : ℕ) = j + 1 ∧ (a : ℕ) ≤ j) →
        (g : Matrix (Fin (r + 1)) (Fin (r + 1)) A) a b = (1 : Matrix _ _ A) a b := by
  rw [Subgroup.mem_inf, mem_blockUnipotentSubgroup]
  change _ ∧ (∀ a b, projectionWeight (r + 1) (j + 1) a ≠ projectionWeight (r + 1) (j + 1) b →
    (g : Matrix (Fin (r + 1)) (Fin (r + 1)) A) a b = 0) ↔ _
  constructor
  · rintro ⟨hU, hL⟩ a b hab
    by_cases hle : projectionWeight (r + 1) j a ≤ projectionWeight (r + 1) j b
    · exact hU a b hle
    · rw [projectionWeight_le_iff] at hle
      have hne : a ≠ b := fun h => by subst h; omega
      rw [Matrix.one_apply_ne hne]
      refine hL a b ?_
      simp only [projectionWeight]
      omega
  · intro h
    refine ⟨fun a b hab => h a b ?_, fun a b hab => ?_⟩
    · rw [projectionWeight_le_iff] at hab
      omega
    · have hne : a ≠ b := fun h => hab (congrArg _ h)
      rw [h a b ?_, Matrix.one_apply_ne hne]
      simp only [projectionWeight] at hab
      omega


end Matrix

section ColumnMatrix

variable {A : Type*} [CommRing A] {r : ℕ} (j : ℕ)

/-- The matrix with the entries of `c` in column `j + 1`, rows `≤ j`, and zero elsewhere. -/
def colMatrix (c : Fin (r + 1) → A) : Matrix (Fin (r + 1)) (Fin (r + 1)) A :=
  Matrix.of fun a b => if (a : ℕ) < j + 1 ∧ (b : ℕ) = j + 1 then c a else 0

/-- A vector supported in the first `j + 1` coordinates. -/
def IsColSupported (c : Fin (r + 1) → A) : Prop := ∀ a : Fin (r + 1), j + 1 ≤ (a : ℕ) → c a = 0

theorem colMatrix_apply (c : Fin (r + 1) → A) (a b : Fin (r + 1)) :
    colMatrix j c a b = if (a : ℕ) < j + 1 ∧ (b : ℕ) = j + 1 then c a else 0 := rfl

theorem colMatrix_add (c d : Fin (r + 1) → A) :
    colMatrix j (c + d) = colMatrix j c + colMatrix j d := by
  ext a b
  simp only [colMatrix_apply, Pi.add_apply, Matrix.add_apply]
  split_ifs <;> simp

theorem colMatrix_mul_colMatrix (c d : Fin (r + 1) → A) :
    colMatrix j c * colMatrix j d = 0 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  simp only [colMatrix_apply]
  split_ifs with h1 h2
  · omega
  · simp
  · simp
  · simp

/-- `1 + colMatrix c` is upper unitriangular. -/
theorem isUnitriangular_one_add_colMatrix (c : Fin (r + 1) → A) :
    IsUnitriangular (1 + colMatrix j c) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · have hab' : (b : ℕ) < a := hab
    rw [Matrix.add_apply, Matrix.one_apply_ne (fun h => by subst h; omega), colMatrix_apply,
      ite_eq_right (by omega), add_zero]
  · rw [Matrix.add_apply, Matrix.one_apply_eq, colMatrix_apply, ite_eq_right (by omega), add_zero]

/-- The product of two column unipotent matrices adds the column vectors. -/
theorem one_add_colMatrix_mul (c d : Fin (r + 1) → A) :
    (1 + colMatrix j c) * (1 + colMatrix j d) = 1 + colMatrix j (c + d) := by
  rw [add_mul, one_mul, mul_add, mul_one, colMatrix_mul_colMatrix, add_zero, colMatrix_add]
  abel

/-- Rational padding preserves the support of column vectors. -/
theorem isColSupported_padGL_mulVec {hle : j + 1 ≤ r + 1}
    (g : Matrix.GeneralLinearGroup (Fin (j + 1)) A) {c : Fin (r + 1) → A}
    (hc : IsColSupported j c) :
    IsColSupported j (Matrix.mulVec (padGL hle g : Matrix (Fin (r + 1)) (Fin (r + 1)) A) c) := by
  intro a ha
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [padGL_apply, dite_eq_right (by omega)]
  split_ifs with hak
  · subst hak
    rw [hc a ha, mul_zero]
  · rw [zero_mul]

/-- `diag(g, I)` conjugates column unipotent matrices into column unipotent matrices. -/
theorem padGL_mul_colMatrix {hle : j + 1 ≤ r + 1}
    (g : Matrix.GeneralLinearGroup (Fin (j + 1)) A) {c : Fin (r + 1) → A}
    (hc : IsColSupported j c) :
    (padGL hle g : Matrix (Fin (r + 1)) (Fin (r + 1)) A) * colMatrix j c =
      colMatrix j (Matrix.mulVec (padGL hle g : Matrix (Fin (r + 1)) (Fin (r + 1)) A) c) *
        (padGL hle g : Matrix (Fin (r + 1)) (Fin (r + 1)) A) := by
  have hPc := isColSupported_padGL_mulVec j g (hle := hle) hc
  set P := (padGL hle g : Matrix (Fin (r + 1)) (Fin (r + 1)) A) with hP
  ext a b
  rw [Matrix.mul_apply, Matrix.mul_apply]
  by_cases hb : (b : ℕ) = j + 1
  · have hR : ∑ k, colMatrix j (Matrix.mulVec P c) a k * P k b = Matrix.mulVec P c a := by
      rw [Finset.sum_eq_single b]
      · rw [colMatrix_apply, hP, padGL_apply, dite_eq_right (by omega), ite_eq_left rfl, mul_one, ← hP]
        by_cases ha : (a : ℕ) < j + 1
        · rw [ite_eq_left ⟨ha, hb⟩]
        · rw [ite_eq_right (fun h => ha h.1), hPc a (by omega)]
      · intro k _ hkb
        rw [colMatrix_apply, ite_eq_right (fun h => hkb (Fin.ext (h.2.trans hb.symm))), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ b) h
    have hL : ∑ k, P a k * colMatrix j c k b = Matrix.mulVec P c a := by
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [colMatrix_apply]
      by_cases hk : (k : ℕ) < j + 1
      · rw [ite_eq_left ⟨hk, hb⟩]
      · rw [ite_eq_right (fun h => hk h.1), hc k (by omega), mul_zero]
    rw [hL, hR]
  · rw [Finset.sum_eq_zero (fun k _ => by rw [colMatrix_apply, ite_eq_right (fun h => hb h.2), mul_zero]),
      Finset.sum_eq_zero (fun k _ => ?_)]
    rw [colMatrix_apply]
    by_cases hk : (k : ℕ) = j + 1
    · rw [hP, padGL_apply, dite_eq_right (by omega), ite_eq_right (fun (h : k = b) => hb (h ▸ hk)), mul_zero]
    · rw [ite_eq_right (fun h => hk h.2), zero_mul]

end ColumnMatrix

local instance radicalSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance radicalSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

section Points

variable (F : Type u) [Field F] [NumberField F] {r : ℕ}

/-- An adelic point lies in `Y_(r+1,j)(𝔸)` exactly when its matrix is upper unitriangular with
first `j + 1` columns those of the identity. -/
theorem mem_projectionAdelic_iff (j : ℕ) (x : Points F (r + 1)) :
    x ∈ AdelicSubgroupPoints.adelicPoints F (Scheme F (r + 1)) (projectionUnipotent F (r + 1) j) ↔
      IsUnitriangular ((GeneralLinearGroupPoints.adelicEquiv F (r + 1) x :
          Matrix.GeneralLinearGroup (Fin (r + 1)) (Adeles F)) :
            Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) ∧
        ∀ a b : Fin (r + 1), (b : ℕ) ≤ j →
          ((GeneralLinearGroupPoints.adelicEquiv F (r + 1) x :
            Matrix.GeneralLinearGroup (Fin (r + 1)) (Adeles F)) :
              Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) a b =
            (1 : Matrix _ _ (Adeles F)) a b := by
  rw [← mem_projectionSubgroup_iff]
  exact GroupScheme.GeneralLinear.mem_blockUnipotent_affinePoints_iff
    (CommRingCat.of F) (CommAlgCat.of F (AdeleRing (𝓞 F) F)) (projectionWeight (r + 1) j) x

omit [NumberField F] in
/-- A rational point lies in `Y_(r+1,j)(F)` exactly when its matrix is upper unitriangular with
first `j + 1` columns those of the identity. -/
theorem mem_projectionRational_iff (j : ℕ) (x : RationalGroupPoints F (Scheme F (r + 1))) :
    x ∈ AdelicSubgroupPoints.rationalPoints F (Scheme F (r + 1))
        (projectionUnipotent F (r + 1) j) ↔
      IsUnitriangular ((GeneralLinearGroupPoints.rationalEquiv F (r + 1) x :
          Matrix.GeneralLinearGroup (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) ∧
        ∀ a b : Fin (r + 1), (b : ℕ) ≤ j →
          ((GeneralLinearGroupPoints.rationalEquiv F (r + 1) x :
            Matrix.GeneralLinearGroup (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F)
              a b = (1 : Matrix _ _ F) a b := by
  rw [← mem_projectionSubgroup_iff]
  exact GroupScheme.GeneralLinear.mem_blockUnipotent_affinePoints_iff
    (CommRingCat.of F) (CommAlgCat.of F F) (projectionWeight (r + 1) j) x

/-- Rational reduction of an adelic point of `Y_(r+1,j)`, changing only the columns after
`j`: given `F + D = 𝔸`, some rational `ρ` of the same shape moves every free entry into `D`. -/
theorem exists_projection_reduction {D : Set (Adeles F)}
    (hD : ∀ a : Adeles F, ∃ f : F, algebraMap F (Adeles F) f + a ∈ D) (j : ℕ)
    {N : Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)} (hN : IsUnitriangular N)
    (hNj : ∀ a b : Fin (r + 1), (b : ℕ) ≤ j → N a b = (1 : Matrix _ _ (Adeles F)) a b) :
    ∃ ρ : Matrix (Fin (r + 1)) (Fin (r + 1)) F, IsUnitriangular ρ ∧
      (∀ a b : Fin (r + 1), (b : ℕ) ≤ j → ρ a b = (1 : Matrix _ _ F) a b) ∧
      ∀ a b : Fin (r + 1), a < b → j < (b : ℕ) →
        (ρ.map (algebraMap F (Adeles F)) * N) a b ∈ D := by
  have hcol : ∀ (ρ : Matrix (Fin (r + 1)) (Fin (r + 1)) F) (a b : Fin (r + 1)), (b : ℕ) ≤ j →
      (ρ.map (algebraMap F (Adeles F)) * N) a b = algebraMap F (Adeles F) (ρ a b) := by
    intro ρ a b hb
    rw [Matrix.mul_apply, Finset.sum_eq_single b]
    · rw [hNj b b hb, Matrix.one_apply_eq, mul_one, Matrix.map_apply]
    · intro c _ hcb
      rw [hNj c b hb, Matrix.one_apply_ne hcb, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ b) h
  suffices h : ∀ k : ℕ, ∃ ρ : Matrix (Fin (r + 1)) (Fin (r + 1)) F, IsUnitriangular ρ ∧
      (∀ a b : Fin (r + 1), (b : ℕ) ≤ j → ρ a b = (1 : Matrix _ _ F) a b) ∧
      ∀ a b : Fin (r + 1), a < b → j < (b : ℕ) → (b : ℕ) < k →
        (ρ.map (algebraMap F (Adeles F)) * N) a b ∈ D by
    obtain ⟨ρ, hρ, hρj, h⟩ := h (r + 1)
    exact ⟨ρ, hρ, hρj, fun a b hab hjb => h a b hab hjb b.isLt⟩
  intro k
  induction k with
  | zero =>
    exact ⟨1, isUnitriangular_one, fun a b _ => rfl,
      fun a b _ _ hb => absurd hb (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨ρ, hρ, hρj, h⟩ := ih
    by_cases hk : k < r + 1 ∧ j < k
    · obtain ⟨ρ', hρ', hsame, hnew⟩ :=
        PrimitiveAdelicHeight.exists_column_step F hD hN hρ ⟨k, hk.1⟩
      refine ⟨ρ', hρ', fun a b hb => ?_, fun a b hab hjb hbk => ?_⟩
      · have h1 := hsame a b (Fin.lt_def.mpr (by simp only; omega))
        rw [hcol ρ' a b hb, hcol ρ a b hb, hρj a b hb] at h1
        exact AdeleRing.algebraMap_injective (𝓞 F) F h1
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hbk with hbk | hbk
        · rw [hsame a b (Fin.lt_def.mpr hbk)]
          exact h a b hab hjb hbk
        · obtain rfl : b = ⟨k, hk.1⟩ := Fin.ext hbk
          exact hnew a hab
    · refine ⟨ρ, hρ, hρj, fun a b hab hjb hbk => h a b hab hjb ?_⟩
      have := b.isLt
      omega

/-- The compact set of shapes reached by the rational reduction. -/
theorem isCompact_projectionBox (j : ℕ) {D : Set (Adeles F)} (hD : IsCompact D) :
    IsCompact {M : Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F) | IsUnitriangular M ∧
      (∀ a b : Fin (r + 1), (b : ℕ) ≤ j → M a b = (1 : Matrix _ _ (Adeles F)) a b) ∧
      ∀ a b : Fin (r + 1), a < b → j < (b : ℕ) → M a b ∈ D} := by
  classical
  have h : {M : Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F) | IsUnitriangular M ∧
      (∀ a b : Fin (r + 1), (b : ℕ) ≤ j → M a b = (1 : Matrix _ _ (Adeles F)) a b) ∧
      ∀ a b : Fin (r + 1), a < b → j < (b : ℕ) → M a b ∈ D} =
      Set.pi Set.univ fun a : Fin (r + 1) => Set.pi Set.univ fun b : Fin (r + 1) =>
        if (b : ℕ) ≤ j then ({(1 : Matrix _ _ (Adeles F)) a b} : Set (Adeles F))
        else if a < b then D else if a = b then ({1} : Set (Adeles F)) else {0} := by
    ext M
    constructor
    · rintro ⟨⟨hup, hdiag⟩, hMj, hMD⟩
      refine Set.mem_univ_pi.mpr fun a => Set.mem_univ_pi.mpr fun b => ?_
      split_ifs with h1 h2 h3
      · exact Set.mem_singleton_iff.mpr (hMj a b h1)
      · exact hMD a b h2 (by omega)
      · subst h3
        exact Set.mem_singleton_iff.mpr (hdiag a)
      · exact Set.mem_singleton_iff.mpr
          (hup (lt_of_le_of_ne (not_lt.mp h2) (Ne.symm h3)))
    · intro hM
      have hM' := fun a b => Set.mem_univ_pi.mp (Set.mem_univ_pi.mp hM a) b
      refine ⟨⟨fun a b hab => ?_, fun a => ?_⟩, fun a b hb => ?_, fun a b hab hjb => ?_⟩
      · have hab' : b < a := hab
        have := hM' a b
        split_ifs at this with h1 h2 h3
        · rw [Set.mem_singleton_iff.mp this, Matrix.one_apply_ne (ne_of_gt hab')]
        · exact absurd h2 (not_lt.mpr hab'.le)
        · exact absurd h3 (ne_of_gt hab')
        · exact Set.mem_singleton_iff.mp this
      · have := hM' a a
        split_ifs at this with h1 h2 h3
        · rw [Set.mem_singleton_iff.mp this, Matrix.one_apply_eq]
        · exact absurd h2 (lt_irrefl a)
        · exact Set.mem_singleton_iff.mp this
        · exact absurd rfl h3
      · have := hM' a b
        split_ifs at this
        exact Set.mem_singleton_iff.mp this
      · have := hM' a b
        split_ifs at this with h1
        · omega
        · exact this
  rw [h]
  exact isCompact_univ_pi fun a => isCompact_univ_pi fun b => by
    split_ifs
    exacts [isCompact_singleton, hD, isCompact_singleton, isCompact_singleton]

/-- `Y_(r+1,j)(F) \ Y_(r+1,j)(𝔸)` is compact. -/
theorem compactSpace_projectionRationalQuotient (j : ℕ) :
    CompactSpace (AdelicSubgroupPoints.RationalQuotient F (Scheme F (r + 1))
      (projectionUnipotent F (r + 1) j)) := by
  obtain ⟨D, hDc, hD⟩ := AdelicGroupPoints.exists_isCompact_algebraMap_add_mem F
  set Ω : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) :=
    {M | IsUnitriangular M ∧
      (∀ a b : Fin (r + 1), (b : ℕ) ≤ j → M a b = (1 : Matrix _ _ (Adeles F)) a b) ∧
      ∀ a b : Fin (r + 1), a < b → j < (b : ℕ) → M a b ∈ D} with hΩdef
  have hΩc : IsCompact Ω := isCompact_projectionBox F j hDc
  let f : Ω → Matrix.GeneralLinearGroup (Fin (r + 1)) (Adeles F) := fun M =>
    unitriangularUnit (M : Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) M.property.1
  have hf : Continuous f :=
    Units.continuous_iff.mpr ⟨continuous_subtype_val, continuous_subtype_val.matrix_adjugate⟩
  have : CompactSpace Ω := isCompact_iff_compactSpace.mp hΩc
  let K : Set (AdelicSubgroupPoints.adelicPoints F (Scheme F (r + 1))
      (projectionUnipotent F (r + 1) j)) :=
    Subtype.val ⁻¹' (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1) ⁻¹' Set.range f)
  have hK : IsCompact K :=
    (projectionUnipotentClosed F (r + 1) j).isClosedEmbedding_subtypeVal.isCompact_preimage
      ((GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).isCompact_preimage.mpr
        (isCompact_range hf))
  have hsurj : LeftCosetSpace.mk
      (AdelicSubgroupPoints.rationalSubgroup F (Scheme F (r + 1))
        (projectionUnipotent F (r + 1) j)) '' K = Set.univ := by
    refine Set.eq_univ_of_forall fun q => ?_
    obtain ⟨u, rfl⟩ := LeftCosetSpace.mk_surjective _ q
    obtain ⟨hu, huj⟩ := (mem_projectionAdelic_iff F j u.val).mp u.property
    obtain ⟨c, hc, hcj, hcD⟩ := exists_projection_reduction F hD j hu huj
    let k0 : RationalGroupPoints F (Scheme F (r + 1)) :=
      (GeneralLinearGroupPoints.rationalEquiv F (r + 1)).symm (unitriangularUnit c hc)
    have hk0 : k0 ∈ AdelicSubgroupPoints.rationalPoints F (Scheme F (r + 1))
        (projectionUnipotent F (r + 1) j) := by
      rw [mem_projectionRational_iff]
      simpa [k0, unitriangularUnit] using And.intro hc hcj
    let k : AdelicSubgroupPoints.rationalSubgroup F (Scheme F (r + 1))
        (projectionUnipotent F (r + 1) j) :=
      ⟨AdelicSubgroupPoints.rational F _ _ ⟨k0, hk0⟩, ⟨_, rfl⟩⟩
    have hprod : ((GeneralLinearGroupPoints.adelicEquiv F (r + 1)
        (AdelicGroupPoints.rational F (Scheme F (r + 1)) k0 * u.val) :
          Matrix.GeneralLinearGroup (Fin (r + 1)) (Adeles F)) :
            Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) =
        c.map (algebraMap F (Adeles F)) *
          ((GeneralLinearGroupPoints.adelicEquiv F (r + 1) u.val :
            Matrix.GeneralLinearGroup (Fin (r + 1)) (Adeles F)) :
              Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) := by
      rw [map_mul, Units.val_mul, GeneralLinearGroupPoints.adelicEquiv_rational]
      congr 1
      ext a b
      simp [k0, unitriangularUnit]
    have hmem : ((GeneralLinearGroupPoints.adelicEquiv F (r + 1)
        (AdelicGroupPoints.rational F (Scheme F (r + 1)) k0 * u.val) :
          Matrix.GeneralLinearGroup (Fin (r + 1)) (Adeles F)) :
            Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) ∈ Ω := by
      have hmemY := (mem_projectionAdelic_iff F j _).mp
        ((k : AdelicSubgroupPoints.adelicPoints F (Scheme F (r + 1))
          (projectionUnipotent F (r + 1) j)) * u).property
      refine ⟨hmemY.1, hmemY.2, ?_⟩
      rw [hprod]
      exact hcD
    refine ⟨(k : AdelicSubgroupPoints.adelicPoints F (Scheme F (r + 1))
        (projectionUnipotent F (r + 1) j)) * u, ?_, LeftCosetSpace.mk_subgroup_mul _ k u⟩
    refine ⟨⟨_, hmem⟩, ?_⟩
    apply Units.ext
    rfl
  refine ⟨?_⟩
  rw [← hsurj]
  exact hK.image (LeftCosetSpace.continuous_mk _)

end Points

end Langlands.Global.RankinSelbergGlobal.Unfolding
