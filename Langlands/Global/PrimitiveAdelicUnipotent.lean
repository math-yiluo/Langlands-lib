import Langlands.Global.AdelicGL
import Langlands.Global.TriangularRationalQuotientCompact

/-! # Rational reduction of adelic unitriangular matrices -/

noncomputable section

universe u

open scoped Matrix

namespace Langlands.Global.PrimitiveAdelicHeight

/-! ## Unitriangular matrices -/

section Unitriangular

variable {R : Type*} [CommRing R] {n : ℕ}

/-- An upper unitriangular matrix: upper triangular with every diagonal entry `1`. -/
def IsUnitriangular (A : Matrix (Fin n) (Fin n) R) : Prop :=
  A.IsUpperTriangular ∧ ∀ i, A i i = 1

theorem isUnitriangular_one : IsUnitriangular (1 : Matrix (Fin n) (Fin n) R) :=
  ⟨Matrix.blockTriangular_one, fun i => Matrix.one_apply_eq i⟩

theorem IsUnitriangular.mul {A B : Matrix (Fin n) (Fin n) R} (hA : IsUnitriangular A)
    (hB : IsUnitriangular B) : IsUnitriangular (A * B) := by
  refine ⟨Matrix.BlockTriangular.mul hA.1 hB.1, fun i => ?_⟩
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hA.2 i, hB.2 i, mul_one]
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with hk | hk
    · rw [hA.1 hk, zero_mul]
    · rw [hB.1 hk, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem IsUnitriangular.map {S : Type*} [CommRing S] (f : R →+* S)
    {A : Matrix (Fin n) (Fin n) R} (hA : IsUnitriangular A) : IsUnitriangular (A.map f) :=
  ⟨fun i j hij => by rw [Matrix.map_apply, hA.1 hij, map_zero],
    fun i => by rw [Matrix.map_apply, hA.2 i, map_one]⟩

theorem IsUnitriangular.det_eq_one {A : Matrix (Fin n) (Fin n) R} (hA : IsUnitriangular A) :
    A.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular hA.1]
  exact Finset.prod_eq_one fun i _ => hA.2 i

end Unitriangular

/-! ## Reduction by rational unitriangular matrices -/

variable (F : Type u) [Field F] [NumberField F] {n : ℕ}

/-- The unitriangular adelic matrices whose entries above the diagonal lie in `D`. -/
def unitriangularBox (D : Set (Adeles F)) : Set (Matrix (Fin n) (Fin n) (Adeles F)) :=
  {M | IsUnitriangular M ∧ ∀ i j, i < j → M i j ∈ D}

theorem isCompact_unitriangularBox {D : Set (Adeles F)} (hD : IsCompact D) :
    IsCompact (unitriangularBox F D (n := n)) := by
  classical
  have h : unitriangularBox F D (n := n) = Set.pi Set.univ fun i => Set.pi Set.univ fun j =>
      if i < j then D else if i = j then ({1} : Set (Adeles F)) else {0} := by
    ext M
    change (IsUnitriangular M ∧ ∀ i j, i < j → M i j ∈ D) ↔
      ∀ i, i ∈ Set.univ → ∀ j, j ∈ Set.univ → M i j ∈
        (if i < j then D else if i = j then ({1} : Set (Adeles F)) else {0})
    simp only [Set.mem_univ, true_implies]
    constructor
    · rintro ⟨⟨hup, hdiag⟩, hMD⟩ i j
      split_ifs with h1 h2
      · exact hMD i j h1
      · subst h2
        exact Set.mem_singleton_iff.mpr (hdiag i)
      · exact Set.mem_singleton_iff.mpr (hup (lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)))
    · intro hM
      refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j hij => ?_⟩
      · have hji : j < i := hij
        have := hM i j
        rw [ite_eq_right (not_lt.mpr hji.le), ite_eq_right (ne_of_gt hji)] at this
        exact Set.mem_singleton_iff.mp this
      · have := hM i i
        rw [ite_eq_right (lt_irrefl i), ite_eq_left rfl] at this
        exact Set.mem_singleton_iff.mp this
      · have := hM i j
        rw [ite_eq_left hij] at this
        exact this
  rw [h]
  exact isCompact_univ_pi fun i => isCompact_univ_pi fun j => by
    split_ifs
    exacts [hD, isCompact_singleton, isCompact_singleton]

/-- One column step: change column `m` of the rational unitriangular `μ` so that the
entries of `μ * N` above the diagonal in column `m` lie in `D`, without changing the
columns before `m`. -/
theorem exists_column_step {D : Set (Adeles F)}
    (hD : ∀ a : Adeles F, ∃ f : F, algebraMap F (Adeles F) f + a ∈ D)
    {N : Matrix (Fin n) (Fin n) (Adeles F)} (hN : IsUnitriangular N)
    {μ : Matrix (Fin n) (Fin n) F} (hμ : IsUnitriangular μ) (m : Fin n) :
    ∃ μ' : Matrix (Fin n) (Fin n) F, IsUnitriangular μ' ∧
      (∀ i j, j < m → (μ'.map (algebraMap F (Adeles F)) * N) i j =
        (μ.map (algebraMap F (Adeles F)) * N) i j) ∧
      ∀ i, i < m → (μ'.map (algebraMap F (Adeles F)) * N) i m ∈ D := by
  classical
  choose r hr using fun i => hD ((μ.map (algebraMap F (Adeles F)) * N) i m)
  set E : Matrix (Fin n) (Fin n) F := Matrix.of fun i j => if j = m ∧ i < m then r i else 0
    with hEdef
  have hE : ∀ i j, (E.map (algebraMap F (Adeles F)) * N) i j =
      if i < m then algebraMap F (Adeles F) (r i) * N m j else 0 := by
    intro i j
    rw [Matrix.mul_apply, Finset.sum_eq_single m]
    · rw [Matrix.map_apply, hEdef, Matrix.of_apply]
      by_cases hi : i < m
      · rw [ite_eq_left ⟨rfl, hi⟩, ite_eq_left hi]
      · rw [ite_eq_right fun h => hi h.2, ite_eq_right hi, map_zero, zero_mul]
    · intro k _ hkm
      rw [Matrix.map_apply, hEdef, Matrix.of_apply, ite_eq_right fun h => hkm h.1, map_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ m) h
  have hmap : (μ + E).map (algebraMap F (Adeles F)) =
      μ.map (algebraMap F (Adeles F)) + E.map (algebraMap F (Adeles F)) :=
    Matrix.map_add _ (map_add (algebraMap F (Adeles F))) μ E
  refine ⟨μ + E, ⟨fun i j hij => ?_, fun i => ?_⟩, fun i j hj => ?_, fun i hi => ?_⟩
  · rw [Matrix.add_apply, hμ.1 hij, hEdef, Matrix.of_apply, zero_add, ite_eq_right]
    rintro ⟨rfl, h⟩
    exact lt_irrefl _ (lt_trans hij h)
  · rw [Matrix.add_apply, hμ.2 i, hEdef, Matrix.of_apply, ite_eq_right, add_zero]
    rintro ⟨rfl, h⟩
    exact lt_irrefl _ h
  · rw [hmap, Matrix.add_mul, Matrix.add_apply, hE]
    split_ifs
    · rw [hN.1 hj, mul_zero, add_zero]
    · rw [add_zero]
  · rw [hmap, Matrix.add_mul, Matrix.add_apply, hE, ite_eq_left hi, hN.2 m, mul_one, add_comm]
    exact hr i

/-- Given `F + D = 𝔸_F`, every adelic unitriangular `N` has a rational unitriangular
`μ` such that every entry of `μ * N` above the diagonal lies in `D`. -/
theorem exists_unitriangular_mul_mem {D : Set (Adeles F)}
    (hD : ∀ a : Adeles F, ∃ f : F, algebraMap F (Adeles F) f + a ∈ D)
    {N : Matrix (Fin n) (Fin n) (Adeles F)} (hN : IsUnitriangular N) :
    ∃ μ : Matrix (Fin n) (Fin n) F, IsUnitriangular μ ∧
      ∀ i j, i < j → (μ.map (algebraMap F (Adeles F)) * N) i j ∈ D := by
  suffices h : ∀ m : ℕ, ∃ μ : Matrix (Fin n) (Fin n) F, IsUnitriangular μ ∧
      ∀ i j : Fin n, i < j → j.val < m → (μ.map (algebraMap F (Adeles F)) * N) i j ∈ D by
    obtain ⟨μ, hμ, h⟩ := h n
    exact ⟨μ, hμ, fun i j hij => h i j hij j.isLt⟩
  intro m
  induction m with
  | zero => exact ⟨1, isUnitriangular_one, fun i j _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ m ih =>
    obtain ⟨μ, hμ, h⟩ := ih
    by_cases hm : m < n
    · obtain ⟨μ', hμ', hsame, hnew⟩ := exists_column_step F hD hN hμ ⟨m, hm⟩
      refine ⟨μ', hμ', fun i j hij hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
      · rw [hsame i j (Fin.lt_def.mpr hj)]
        exact h i j hij hj
      · obtain rfl : j = ⟨m, hm⟩ := Fin.ext hj
        exact hnew i hij
    · exact ⟨μ, hμ, fun i j hij _ => h i j hij (lt_of_lt_of_le j.isLt (not_lt.mp hm))⟩

/-- **Compact reduction of adelic unitriangular matrices.** There is a compact set `Ω` of
unitriangular adelic matrices such that every adelic unitriangular `N` becomes an element
of `Ω` after left multiplication by some rational unitriangular `μ`. -/
theorem exists_isCompact_unitriangular_reduction (n : ℕ) :
    ∃ Ω : Set (Matrix (Fin n) (Fin n) (Adeles F)), IsCompact Ω ∧
      (∀ M ∈ Ω, IsUnitriangular M) ∧
      ∀ N : Matrix (Fin n) (Fin n) (Adeles F), IsUnitriangular N →
        ∃ μ : Matrix (Fin n) (Fin n) F, IsUnitriangular μ ∧
          μ.map (algebraMap F (Adeles F)) * N ∈ Ω := by
  obtain ⟨D, hDc, hD⟩ := AdelicGroupPoints.exists_isCompact_algebraMap_add_mem F
  refine ⟨unitriangularBox F D, isCompact_unitriangularBox F hDc, fun M hM => hM.1,
    fun N hN => ?_⟩
  obtain ⟨μ, hμ, hμN⟩ := exists_unitriangular_mul_mem F hD hN
  exact ⟨μ, hμ, (hμ.map (algebraMap F (Adeles F))).mul hN, hμN⟩

end Langlands.Global.PrimitiveAdelicHeight
