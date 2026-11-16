import Langlands.Global.RankinSelberg.UnfoldingGL
import Langlands.Global.AdelicGLStandardCompact

/-! # Padding preserves the standard adelic compact subgroup

Adapted from Worker 269's compact-padding draft, with the gauge-dependent
parts removed by Worker 254.
-/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal NNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Unfolding

section Matrices

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Padding commutes with an entrywise ring homomorphism. -/
theorem map_padGL {m n : ℕ} (h : m ≤ n) (f : R →+* S)
    (g : Matrix.GeneralLinearGroup (Fin m) R) :
    Matrix.GeneralLinearGroup.map f (padGL h g) =
      padGL h (Matrix.GeneralLinearGroup.map f g) := by
  apply Units.ext
  ext i j
  change f ((padGL h g).val i j) = _
  rw [padGL_apply, padGL_apply]
  split_ifs <;> simp_all [Matrix.GeneralLinearGroup.map_apply]

/-- Padding preserves entrywise membership in a subring. -/
theorem padGL_entries_mem {m n : ℕ} (h : m ≤ n) (O : Subring R)
    (g : Matrix.GeneralLinearGroup (Fin m) R) (hg : ∀ i j, g.val i j ∈ O) :
    ∀ i j, (padGL h g).val i j ∈ O := by
  intro i j
  rw [padGL_apply]
  split_ifs
  · exact hg _ _
  · exact O.zero_mem
  · exact O.one_mem
  · exact O.zero_mem

/-- Padding preserves unitarity of a matrix unit. -/
theorem unitary_padGL [StarRing R] {m n : ℕ} (h : m ≤ n)
    (g : Matrix.GeneralLinearGroup (Fin m) R)
    (hg : g.val ∈ Matrix.unitaryGroup (Fin m) R) :
    (padGL h g).val ∈ Matrix.unitaryGroup (Fin n) R := by
  have hs : star (padGL h g).val = (padGL h g⁻¹).val := by
    have hgi : g⁻¹.val = star g.val :=
      Units.inv_eq_of_mul_eq_one_right (Matrix.mem_unitaryGroup_iff.mp hg)
    ext i j
    change star ((padGL h g).val j i) = _
    rw [padGL_apply, padGL_apply]
    by_cases hi : (i : ℕ) < m <;> by_cases hj : (j : ℕ) < m
    · simp only [dite_eq_left hi, dite_eq_left hj]
      exact (congrArg (fun A => A ⟨i, hi⟩ ⟨j, hj⟩) hgi).symm
    · have hij : i ≠ j := fun he => by subst j; exact hj hi
      simp [hi, hj, hij.symm]
    · have hij : j ≠ i := fun he => by subst j; exact hi hj
      simp [hi, hj, hij.symm]
    · by_cases hij : i = j
      · subst j
        simp [hi]
      · simp [hi, hj, hij, Ne.symm hij]
  rw [Matrix.mem_unitaryGroup_iff, hs, ← Units.val_mul, ← map_mul,
    mul_inv_cancel, map_one, Units.val_one]

end Matrices

variable (F : Type u) [Field F] [NumberField F]

/-- Padding carries the finite integral compact subgroup into the larger one. -/
theorem padGL_mem_standardIntegral {m n : ℕ} (h : m ≤ n)
    (g : FiniteAdelicGL F m) (hg : g ∈ FiniteAdelicGL.standardIntegral F m) :
    padGL h g ∈ FiniteAdelicGL.standardIntegral F n := by
  change (∀ i j, g.val i j ∈ FiniteAdelicGL.integralAdeles F) ∧
    (∀ i j, g⁻¹.val i j ∈ FiniteAdelicGL.integralAdeles F) at hg
  change (∀ i j, (padGL h g).val i j ∈ FiniteAdelicGL.integralAdeles F) ∧
    (∀ i j, (padGL h g)⁻¹.val i j ∈ FiniteAdelicGL.integralAdeles F)
  refine ⟨padGL_entries_mem h _ g hg.1, ?_⟩
  simpa only [map_inv] using padGL_entries_mem h (FiniteAdelicGL.integralAdeles F) g⁻¹ hg.2

omit [NumberField F] in
/-- Padding carries the infinite orthogonal-unitary subgroup into the larger one. -/
theorem padGL_mem_standardInfiniteCompact {m n : ℕ} (h : m ≤ n)
    (g : InfiniteAdelicGL F m) (hg : g ∈ standardInfiniteCompact F m) :
    padGL h g ∈ standardInfiniteCompact F n := by
  rw [mem_standardInfiniteCompact_iff] at hg ⊢
  constructor
  · intro v
    change (Matrix.GeneralLinearGroup.map (PrimitiveAdelicHeight.realCoord v)
      (Matrix.GeneralLinearGroup.map (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom
        (padGL h g))).val ∈ Matrix.unitaryGroup (Fin n) ℝ
    rw [map_padGL, map_padGL]
    exact unitary_padGL h _ (hg.1 v)
  · intro v
    change (Matrix.GeneralLinearGroup.map (PrimitiveAdelicHeight.complexCoord v)
      (Matrix.GeneralLinearGroup.map (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom
        (padGL h g))).val ∈ Matrix.unitaryGroup (Fin n) ℂ
    rw [map_padGL, map_padGL]
    exact unitary_padGL h _ (hg.2 v)

/-- Padding carries the standard adelic compact subgroup into the larger one. -/
theorem padGL_mem_standardCompact {m n : ℕ} (h : m ≤ n)
    (g : AdelicGL F m) (hg : g ∈ PrimitiveAdelicHeight.standardCompact F m) :
    padGL h g ∈ PrimitiveAdelicHeight.standardCompact F n := by
  rw [PrimitiveAdelicHeight.mem_standardCompact_iff] at hg ⊢
  constructor
  · change Matrix.GeneralLinearGroup.map _ (padGL h g) ∈ standardInfiniteCompact F n
    erw [map_padGL]
    exact padGL_mem_standardInfiniteCompact F h _ hg.1
  · change Matrix.GeneralLinearGroup.map _ (padGL h g) ∈ FiniteAdelicGL.standardIntegral F n
    erw [map_padGL]
    exact padGL_mem_standardIntegral F h _ hg.2

/-- Padding restricted to the actual standard compact matrix subgroups. -/
def padGLStandardCompactHom {m n : ℕ} (h : m ≤ n) :
    PrimitiveAdelicHeight.standardCompact F m →*
      PrimitiveAdelicHeight.standardCompact F n where
  toFun g := ⟨padGL h g.val, padGL_mem_standardCompact F h g.val g.property⟩
  map_one' := Subtype.ext (map_one (padGL h))
  map_mul' g g' := Subtype.ext (map_mul (padGL h) g.val g'.val)

@[simp]
theorem coe_padGLStandardCompactHom {m n : ℕ} (h : m ≤ n)
    (g : PrimitiveAdelicHeight.standardCompact F m) :
    (padGLStandardCompactHom F h g : AdelicGL F n) = padGL h (g : AdelicGL F m) := rfl

/-- On actual group-scheme points, padding preserves standard compact
membership after the published adelic matrix comparison. -/
theorem pad_mem_standardCompact {m n : ℕ} (h : m ≤ n)
    (g : Points F m)
    (hg : GeneralLinearGroupPoints.adelicEquiv F m g ∈
      PrimitiveAdelicHeight.standardCompact F m) :
    GeneralLinearGroupPoints.adelicEquiv F n (pad F h g) ∈
      PrimitiveAdelicHeight.standardCompact F n := by
  rw [adelicEquiv_pad]
  exact padGL_mem_standardCompact F h _ hg

end Langlands.Global.RankinSelbergGlobal
