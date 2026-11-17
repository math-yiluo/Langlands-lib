import Langlands.Global.RankinSelberg.AdelicRowMajorant
import Langlands.Global.RankinSelberg.EqualAnalyticThetaBound
import Langlands.Global.RankinSelberg.EqualIntegrals
import Langlands.GroupScheme.Rational.GeneralLinearCharacterMatrices

/-! # A Schwartz majorant for compact translates of a coordinate row -/

noncomputable section
universe u
open NumberField Set
open scoped Classical CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Global Langlands.Automorphic.CuspidalWhittaker

local instance compactRowSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _

variable (F : Type u) [Field F] [NumberField F]

/-- Compact right translates of a Schwartz--Bruhat function admit one
Schwartz--Bruhat majorant on the original row space. -/
theorem exists_compact_row_majorant [CompactSpace (AdeleQuotient F)]
    (n : ℕ) {Φ : RowVector F n → ℂ} (hΦ : Φ ∈ schwartzBruhat F n)
    {Q : Set (AdelicGL F n)} (hQ : IsCompact Q) :
    ∃ φ : RowVector F n → ℂ, φ ∈ schwartzBruhat F n ∧
      ∀ (x : RowVector F n) (q : AdelicGL F n), q ∈ Q →
        ‖Φ (x * (q : Matrix (Fin n) (Fin n) (Adeles F)))‖ ≤ ‖φ x‖ := by
  let J := RowVector F n × Q
  let z : J → RowVector F n := fun j => j.1
  let w : J → ℝ := fun j =>
    ‖Φ (j.1 * (j.2.1 : Matrix (Fin n) (Fin n) (Adeles F)))‖
  have hdom := (EqualAnalytic.schwartzBruhat_properties F n hΦ).2.2
  obtain ⟨d, hd, _, hsupp, _⟩ := EqualAnalytic.exists_uniform_dominated F n hdom hQ 0
  have hrapid : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ j, (1 + ‖archimedeanCoordinates F n (z j)‖) ^ N * w j ≤ C := by
    intro N
    obtain ⟨_, _, C, _, hC⟩ := EqualAnalytic.exists_uniform_dominated F n hdom hQ N
    exact ⟨max C 0, le_max_right _ _, fun j =>
      (hC j.1 j.2.1 j.2.2).trans (le_max_left C 0)⟩
  have hdenom : ∀ j, w j ≠ 0 →
      finiteCoordinates F n (z j) ∈
        SchwartzMajorant.denominatorRows F n (algebraMap (𝓞 F) F d) := by
    intro j hj i
    have hn : Φ (j.1 * (j.2.1 : Matrix (Fin n) (Fin n) (Adeles F))) ≠ 0 := by
      intro h
      exact hj (by simp [w, h])
    rw [← IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeles F) d]
    exact hsupp j.1 j.2.1 j.2.2 hn i
  obtain ⟨φ, hφ, hbound, _⟩ := SchwartzMajorant.exists_schwartzBruhat_majorant F
    z w (fun _ => norm_nonneg _) hrapid
    (algebraMap (𝓞 F) F d) (RingOfIntegers.coe_ne_zero_iff.mpr hd) hdenom
  exact ⟨φ, hφ, fun x q hq => hbound (x, ⟨q, hq⟩)⟩

/-- A row supported in one specified coordinate. -/
def coordinateRow (n : ℕ) (i : Fin n) (a : Adeles F) : RowVector F n :=
  Matrix.of fun _ j => if j = i then a else 0

/-- The one-dimensional row associated to an adele. -/
def singleRow (a : Adeles F) : RowVector F 1 := Matrix.of fun _ _ => a

theorem archimedean_singleRow_le_coordinateRow (n : ℕ) (i : Fin n) (a : Adeles F) :
    ‖archimedeanCoordinates F 1 (singleRow F a)‖ ≤
      ‖archimedeanCoordinates F n (coordinateRow F n i a)‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun _ => ?_
  simpa [archimedeanCoordinates, singleRow, coordinateRow] using
    norm_le_pi_norm (archimedeanCoordinates F n (coordinateRow F n i a)) i

/-- A single Schwartz–Bruhat function bounds all compact right translates
of a Schwartz–Bruhat function restricted to a coordinate line. -/
theorem exists_compact_coordinateRow_majorant [CompactSpace (AdeleQuotient F)]
    (n : ℕ) (i : Fin n) {Φ : RowVector F n → ℂ} (hΦ : Φ ∈ schwartzBruhat F n)
    {Q : Set (AdelicGL F n)} (hQ : IsCompact Q) :
    ∃ φ : RowVector F 1 → ℂ, φ ∈ schwartzBruhat F 1 ∧
      ∀ (a : Adeles F) (q : AdelicGL F n), q ∈ Q →
        ‖Φ (coordinateRow F n i a *
          (q : Matrix (Fin n) (Fin n) (Adeles F)))‖ ≤ ‖φ (singleRow F a)‖ := by
  let J := Adeles F × Q
  let z : J → RowVector F 1 := fun j => singleRow F j.1
  let w : J → ℝ := fun j => ‖Φ (coordinateRow F n i j.1 *
    (j.2.1 : Matrix (Fin n) (Fin n) (Adeles F)))‖
  have hw : ∀ j, 0 ≤ w j := fun _ => norm_nonneg _
  have hdom := (EqualAnalytic.schwartzBruhat_properties F n hΦ).2.2
  obtain ⟨d, hd, _, hsupp, _⟩ := EqualAnalytic.exists_uniform_dominated F n hdom hQ 0
  have hrapid : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ j, (1 + ‖archimedeanCoordinates F 1 (z j)‖) ^ N * w j ≤ C := by
    intro N
    obtain ⟨_, _, C, _, hC⟩ := EqualAnalytic.exists_uniform_dominated F n hdom hQ N
    refine ⟨max C 0, le_max_right _ _, fun j => ?_⟩
    have hnorm := archimedean_singleRow_le_coordinateRow F n i j.1
    have hnorm' : 1 + ‖archimedeanCoordinates F 1 (z j)‖ ≤
        1 + ‖archimedeanCoordinates F n (coordinateRow F n i j.1)‖ := by
      dsimp only [z]
      linarith
    exact (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) hnorm' N) (hw j)).trans
        ((hC _ j.2.1 j.2.2).trans (le_max_left C 0))
  have hdenom : ∀ j, w j ≠ 0 →
      finiteCoordinates F 1 (z j) ∈
        SchwartzMajorant.denominatorRows F 1 (algebraMap (𝓞 F) F d) := by
    intro j hj k
    have hn : Φ (coordinateRow F n i j.1 *
        (j.2.1 : Matrix (Fin n) (Fin n) (Adeles F))) ≠ 0 := by
      intro h
      apply hj
      simp [w, h]
    have hs := hsupp (coordinateRow F n i j.1) j.2.1 j.2.2 hn i
    rw [← IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeles F) d]
    simpa only [z, singleRow, coordinateRow, finiteCoordinates, Matrix.of_apply,
      ite_true] using hs
  obtain ⟨φ, hφ, hbound, _⟩ := SchwartzMajorant.exists_schwartzBruhat_majorant F
    z w hw hrapid (algebraMap (𝓞 F) F d) (RingOfIntegers.coe_ne_zero_iff.mpr hd) hdenom
  exact ⟨φ, hφ, fun a q hq => hbound (a, ⟨q, hq⟩)⟩

theorem lastRow_mul (r : ℕ) (g q : Points F (r + 1)) :
    lastRow F r (g * q) = lastRow F r g *
      (GeneralLinearGroupPoints.adelicEquiv F (r + 1) q :
        Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) := by
  ext i j
  simp only [lastRow, Matrix.of_apply, map_mul, Units.val_mul, Matrix.mul_apply]

theorem lastRow_diagonalPoint (r : ℕ) (d : Fin (r + 1) → Ideles F) :
    lastRow F r ((GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
      (GroupScheme.GeneralLinear.diagonalMatrixUnits (Adeles F) d)) =
      coordinateRow F (r + 1) (Fin.last r) (d (Fin.last r) : Adeles F) := by
  ext i j
  simp [lastRow, coordinateRow, Matrix.diagonal_apply, eq_comm]

/-- A compact family of right translates admits a common Schwartz bound in
the last coordinate whenever the original last row is supported there. -/
theorem exists_compact_lastRow_majorant [CompactSpace (AdeleQuotient F)]
    (r : ℕ) {Φ : RowVector F (r + 1) → ℂ}
    (hΦ : Φ ∈ schwartzBruhat F (r + 1))
    {Q : Set (Points F (r + 1))} (hQ : IsCompact Q) :
    ∃ φ : RowVector F 1 → ℂ, φ ∈ schwartzBruhat F 1 ∧
      ∀ (a : Adeles F) (g q : Points F (r + 1)), q ∈ Q →
        lastRow F r g = coordinateRow F (r + 1) (Fin.last r) a →
        ‖Φ (lastRow F r (g * q))‖ ≤ ‖φ (singleRow F a)‖ := by
  let E := GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)
  obtain ⟨φ, hφ, hbound⟩ := exists_compact_coordinateRow_majorant F
    (r + 1) (Fin.last r) hΦ (hQ.image E.continuous)
  refine ⟨φ, hφ, fun a g q hq hg => ?_⟩
  rw [lastRow_mul, hg]
  exact hbound a (E q) (mem_image_of_mem E hq)

/-- On a diagonal point the compact-translate bound depends only on the
last diagonal idele. -/
theorem exists_compact_diagonal_lastRow_majorant [CompactSpace (AdeleQuotient F)]
    (r : ℕ) {Φ : RowVector F (r + 1) → ℂ}
    (hΦ : Φ ∈ schwartzBruhat F (r + 1))
    {Q : Set (Points F (r + 1))} (hQ : IsCompact Q) :
    ∃ φ : RowVector F 1 → ℂ, φ ∈ schwartzBruhat F 1 ∧
      ∀ (d : Fin (r + 1) → Ideles F) (q : Points F (r + 1)), q ∈ Q →
        ‖Φ (lastRow F r
          ((GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
            (GroupScheme.GeneralLinear.diagonalMatrixUnits (Adeles F) d) * q))‖ ≤
          ‖φ (singleRow F (d (Fin.last r) : Adeles F))‖ := by
  obtain ⟨φ, hφ, hbound⟩ := exists_compact_lastRow_majorant F r hΦ hQ
  exact ⟨φ, hφ, fun d q hq =>
    hbound _ _ q hq (lastRow_diagonalPoint F r d)⟩

end Langlands.Global.RankinSelbergGlobal
