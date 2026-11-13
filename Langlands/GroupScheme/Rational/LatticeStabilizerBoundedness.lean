import Langlands.GroupScheme.Rational.MatrixEntryBoundedness
import Mathlib.Algebra.Module.Lattice
import Mathlib.RingTheory.Localization.Submodule

/-! # Algebraic boundedness of full-lattice stabilizers -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry ValuativeRel
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

variable {K : Type u} [Field K] [ValuativeRel K]

private theorem finite_valuative_bound (s : Finset K) :
    ∃ b : K, b ≠ 0 ∧ ∀ x ∈ s, x ≤ᵥ b := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨b, hb, h⟩ := ih
    by_cases hab : a ≤ᵥ b
    · exact ⟨b, hb, by simpa only [Finset.mem_insert, forall_eq_or_imp] using ⟨hab, h⟩⟩
    · have hba : b ≤ᵥ a := (vle_total a b).resolve_left hab
      have ha0 : a ≠ 0 := by
        intro ha0
        exact hb (vle_zero_iff.mp (ha0 ▸ hba))
      refine ⟨a, ha0, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact vle_refl _
      · exact (h x hx).trans hba

private def valuationBall (b : K) : Submodule (valuation K).integer K where
  carrier := {x | x ≤ᵥ b}
  zero_mem' := zero_vle _
  add_mem' := vle_add
  smul_mem' r x hx := by
    change (r : K) * x ≤ᵥ b
    simpa only [one_mul] using mul_vle_mul ((valuation K).vle_one_iff.mpr r.property) hx

private theorem fg_valuative_bound
    {L : Submodule (valuation K).integer K} (hL : L.FG) :
    ∃ b : K, b ≠ 0 ∧ ∀ x ∈ L, x ≤ᵥ b := by
  obtain ⟨s, rfl⟩ := hL
  obtain ⟨b, hb, h⟩ := finite_valuative_bound s
  refine ⟨b, hb, ?_⟩
  have hle : Submodule.span (valuation K).integer (s : Set K) ≤ valuationBall b :=
    Submodule.span_le.mpr h
  exact fun x hx => hle hx

variable {n : Type} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- Every coordinate of a finitely generated integral submodule is uniformly bounded. -/
theorem lattice_coordinate_bound
    (Λ : Submodule (valuation K).integer (n → K)) (hΛ : Λ.FG) (i : n) :
    ∃ b : K, b ≠ 0 ∧ ∀ v ∈ Λ, v i ≤ᵥ b := by
  let p : (n → K) →ₗ[(valuation K).integer] K := LinearMap.proj i
  obtain ⟨b, hb, h⟩ := fg_valuative_bound (hΛ.map p)
  exact ⟨b, hb, fun v hv => h (p v) (Submodule.mem_map.mpr ⟨v, hv, rfl⟩)⟩

/-- Matrices preserving a full lattice have uniformly bounded entries.
The bound may depend on the entry, and no topology is used. -/
theorem matrix_entry_bound_of_preserves_lattice
    (Λ : Submodule (valuation K).integer (n → K)) (hΛ : Submodule.IsLattice K Λ)
    (i j : n) :
    ∃ b : K, b ≠ 0 ∧
      ∀ A : Matrix n n K, (∀ v ∈ Λ, A *ᵥ v ∈ Λ) → A i j ≤ᵥ b := by
  classical
  let := hΛ
  let e : n → K := Pi.single j 1
  have he : e ∈ Submodule.span K (Λ : Set (n → K)) := by
    rw [Submodule.IsLattice.span_eq_top]
    trivial
  obtain ⟨v, hv, z, hz⟩ :=
    (IsLocalization.mem_span_iff (nonZeroDivisors (valuation K).integer)).mp he
  have hv' : v ∈ Λ := by simpa only [Submodule.span_eq] using hv
  let a : K := IsLocalization.mk' K 1 z
  have ha : a ≠ 0 := by
    exact (IsFractionRing.mk'_eq_zero_iff_eq_zero).not.mpr one_ne_zero
  obtain ⟨b, hb, h⟩ := lattice_coordinate_bound Λ hΛ.fg i
  refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
  intro A hA
  have hAv : A i j = a * (A *ᵥ v) i := by
    calc
      A i j = (A *ᵥ e) i := by simp [e, Matrix.mulVec_single]
      _ = (A *ᵥ (a • v)) i := by rw [hz]
      _ = a * (A *ᵥ v) i := by rw [Matrix.mulVec_smul]; rfl
  rw [hAv]
  exact mul_vle_mul_right (h (A *ᵥ v) (hA v hv')) a

variable {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffine G.X.left]

/-- A subgroup preserving a full lattice in a closed representation is
algebraically bounded in the original affine group. -/
theorem isAlgebraicallyBounded_of_preserves_lattice
    (ρ : MatrixRepresentation G n) (hρ : IsClosedSubgroup ρ)
    (B : Subgroup (rationalPoints G))
    (Λ : Submodule (valuation K).integer (n → K)) (hΛ : Submodule.IsLattice K Λ)
    (hB : ∀ g ∈ B, ∀ v ∈ Λ, (ρ.rationalMatrix g : Matrix n n K) *ᵥ v ∈ Λ) :
    IsAlgebraicallyBounded K G.X (B : Set (rationalPoints G)) := by
  apply ρ.isAlgebraicallyBounded_of_entries hρ B (fun g hg => B.inv_mem hg)
  intro i j
  obtain ⟨b, hb, h⟩ := matrix_entry_bound_of_preserves_lattice Λ hΛ i j
  exact ⟨b, hb, fun g hg => h (ρ.rationalMatrix g) (hB g hg)⟩

end Langlands.GroupScheme.MatrixRepresentation
