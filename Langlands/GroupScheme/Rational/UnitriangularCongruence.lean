import Langlands.GroupScheme.IntegralModel.GeneralLinearCongruencePoints
import Langlands.GroupScheme.IntegralModel.GeneralLinearLatticeProof
import Langlands.GroupScheme.Rational.UnipotentCompactSubgroups

/-! # Strict congruence bounds after unitriangular diagonal rescaling -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj Matrix ValuativeRel

namespace Langlands.GroupScheme.UnitriangularCongruence

section Diagonal

variable {F : Type u} [Field F] {n : ℕ}

/-- The diagonal matrix with entries the successive powers of the given field unit. -/
def diagonalUnit (t : Fˣ) : GL (Fin n) F where
  val := Matrix.diagonal fun i => (t : F) ^ (i : ℕ)
  inv := Matrix.diagonal fun i => ((t : F) ^ (i : ℕ))⁻¹
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [mul_inv_cancel₀ (pow_ne_zero _ t.ne_zero), Matrix.diagonal_one]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [inv_mul_cancel₀ (pow_ne_zero _ t.ne_zero), Matrix.diagonal_one]

/-- Rescaling by the diagonal powers, as an automorphism of the actual matrix group. -/
def rescale (t : Fˣ) : GL (Fin n) F ≃* GL (Fin n) F :=
  MulAut.conj (diagonalUnit t)⁻¹

theorem rescale_entry (t : Fˣ) (A : GL (Fin n) F) (i j : Fin n) :
    (rescale t A : Matrix (Fin n) (Fin n) F) i j =
      ((t : F) ^ (i : ℕ))⁻¹ * (A : Matrix (Fin n) (Fin n) F) i j *
        (t : F) ^ (j : ℕ) := by
  change (((diagonalUnit t)⁻¹ : GL (Fin n) F) * A * diagonalUnit t :
    GL (Fin n) F) i j = _
  change ((Matrix.diagonal fun i : Fin n => ((t : F) ^ (i : ℕ))⁻¹) *
    (A : Matrix (Fin n) (Fin n) F) *
    (Matrix.diagonal fun j : Fin n => (t : F) ^ (j : ℕ))) i j = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem rescale_entry_of_le (t : Fˣ) (A : GL (Fin n) F) (i j : Fin n) (hij : i ≤ j) :
    (rescale t A : Matrix (Fin n) (Fin n) F) i j =
      (A : Matrix (Fin n) (Fin n) F) i j * (t : F) ^ ((j : ℕ) - (i : ℕ)) := by
  rw [rescale_entry]
  have hj : (j : ℕ) = (i : ℕ) + ((j : ℕ) - (i : ℕ)) := by omega
  conv_lhs => rw [hj, pow_add]
  field_simp

variable [TopologicalSpace F] [IsTopologicalRing F]

/-- The same diagonal rescaling, with the actual topology on invertible matrices. -/
def rescaleContinuous (t : Fˣ) : GL (Fin n) F ≃ₜ* GL (Fin n) F where
  toMulEquiv := rescale t
  continuous_toFun := (continuous_const.mul continuous_id).mul continuous_const
  continuous_invFun := (continuous_const.mul continuous_id).mul continuous_const

end Diagonal

section Compact

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {Γ : Type v} [Group Γ] [TopologicalSpace Γ] {n : ℕ}

/-- A common diagonal rescaling puts every off-diagonal entry on a compact
unitriangular set strictly inside the maximal ideal. -/
theorem exists_rescale_strict_entries
    (φ : Γ →* GL (Fin n) F) (hφ : Continuous φ)
    (hlow : ∀ x i j, j < i → (φ x : Matrix (Fin n) (Fin n) F) i j = 0)
    (C : Set Γ) (hC : IsCompact C) :
    ∃ t : Fˣ, ∀ x ∈ C, ∀ i j, i ≠ j →
      ValuativeRel.valuation F ((rescale t (φ x) : Matrix (Fin n) (Fin n) F) i j) < 1 := by
  classical
  let v := ValuativeRel.valuation F
  have hent : ∀ i j, Continuous fun x : Γ => (φ x : Matrix (Fin n) (Fin n) F) i j :=
    fun i j => (continuous_apply j).comp ((continuous_apply i).comp
      ((Units.continuous_val (M := Matrix (Fin n) (Fin n) F)).comp hφ))
  let D : Set F := ⋃ i, ⋃ j, (fun x => (φ x : Matrix (Fin n) (Fin n) F) i j) '' C
  have hD : IsCompact D := isCompact_iUnion fun i => isCompact_iUnion fun j =>
    hC.image (hent i j)
  obtain ⟨b, -, hb⟩ := IsCompact.exists_valuative_bound hD
  obtain ⟨c, hc0, hbc, hc1⟩ : ∃ c : F, c ≠ 0 ∧ v b ≤ v c ∧ 1 ≤ v c := by
    rcases le_total (v b) 1 with h | h
    · exact ⟨1, one_ne_zero, by rwa [map_one], (map_one v).ge⟩
    · refine ⟨b, ?_, le_rfl, h⟩
      rintro rfl
      rw [map_zero] at h
      exact one_ne_zero (le_antisymm h zero_le)
  obtain ⟨δ, hδ0, hδ1⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := F)
  obtain ⟨d, hd⟩ := ValuativeRel.valuation_surjective δ
  have hd0 : d ≠ 0 := by
    intro h
    have : δ = 0 := by simpa only [h, map_zero] using hd.symm
    exact hδ0.ne' this
  let t : Fˣ := Units.mk0 (d * c⁻¹) (mul_ne_zero hd0 (inv_ne_zero hc0))
  have htc : v (t : F) * v c = δ := by
    change v (d * c⁻¹) * v c = δ
    rw [← map_mul, mul_assoc, inv_mul_cancel₀ hc0, mul_one, hd]
  have ht1 : v (t : F) ≤ 1 := by
    calc v (t : F) = v (t : F) * 1 := (mul_one _).symm
      _ ≤ v (t : F) * v c := mul_le_mul' le_rfl hc1
      _ = δ := htc
      _ ≤ 1 := hδ1.le
  refine ⟨t, fun x hx i j hij => ?_⟩
  rcases lt_or_gt_of_ne hij with hij | hji
  · rw [rescale_entry_of_le t (φ x) i j hij.le, map_mul, map_pow]
    have hk : (j : ℕ) - (i : ℕ) ≠ 0 := by
      have : (i : ℕ) < j := hij
      omega
    have hm : v ((φ x : Matrix (Fin n) (Fin n) F) i j) ≤ v c :=
      ((v.vle_iff_le).mp (hb _ (Set.mem_iUnion.mpr ⟨i,
        Set.mem_iUnion.mpr ⟨j, ⟨x, hx, rfl⟩⟩⟩))).trans hbc
    calc v ((φ x : Matrix (Fin n) (Fin n) F) i j) * v (t : F) ^ ((j : ℕ) - (i : ℕ))
        ≤ v c * v (t : F) := mul_le_mul' hm (pow_le_of_le_one zero_le ht1 hk)
      _ = δ := by rw [mul_comm]; exact htc
      _ < 1 := hδ1
  · rw [rescale_entry, hlow x i j hji, mul_zero, zero_mul, map_zero]
    exact zero_lt_one

end Compact

section Congruence

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}

/-- Actual integral matrices whose difference from the identity has strictly
small entries give points of the original standard principal congruence subgroup. -/
theorem mem_standardCongruence_of_entries (A : GL (Fin n) F)
    (hA : ∀ i j, ValuativeRel.valuation F ((A : Matrix (Fin n) (Fin n) F) i j) ≤ 1)
    (hAi : ∀ i j, ValuativeRel.valuation F ((A⁻¹ : GL (Fin n) F) i j) ≤ 1)
    (hc : ∀ i j, ValuativeRel.valuation F
      ((A : Matrix (Fin n) (Fin n) F) i j - (1 : Matrix (Fin n) (Fin n) F) i j) < 1) :
    (GeneralLinear.rationalPointsEquiv n (CommRingCat.of F)).symm A ∈
      (GeneralLinear.standardIntegralModel ↥𝒪[F] F (Fin n)).congruenceSubgroupAt 1 := by
  let C : Matrix (Fin n) (Fin n) ↥𝒪[F] := fun i j => ⟨A i j, hA i j⟩
  let D : Matrix (Fin n) (Fin n) ↥𝒪[F] := fun i j => ⟨(A⁻¹ : GL (Fin n) F) i j, hAi i j⟩
  obtain ⟨B, hB⟩ := (GeneralLinear.mem_range_map_iff_exists_map (R := ↥𝒪[F]) A).mpr
    ⟨⟨C, rfl⟩, ⟨D, rfl⟩⟩
  have hBe (i j : Fin n) : (((B : Matrix (Fin n) (Fin n) ↥𝒪[F]) i j) : F) = A i j :=
    congrArg (fun Z : GL (Fin n) F => Z i j) hB
  have hBc : ∀ i j, (B : Matrix (Fin n) (Fin n) ↥𝒪[F]) i j -
      (1 : Matrix (Fin n) (Fin n) ↥𝒪[F]) i j ∈ (IsLocalRing.maximalIdeal ↥𝒪[F]) ^ (1 : ℕ) := by
    intro i j
    rw [pow_one, IsLocalRing.mem_maximalIdeal]
    change ¬ IsUnit ((B : Matrix (Fin n) (Fin n) ↥𝒪[F]) i j -
      (1 : Matrix (Fin n) (Fin n) ↥𝒪[F]) i j)
    rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    change ValuativeRel.valuation F
      ((((B : Matrix (Fin n) (Fin n) ↥𝒪[F]) i j : ↥𝒪[F]) : F) -
        (((1 : Matrix (Fin n) (Fin n) ↥𝒪[F]) i j : ↥𝒪[F]) : F)) < 1
    rw [hBe]
    simpa only [Matrix.one_apply, apply_ite, Subring.coe_one, Subring.coe_zero] using hc i j
  let y := GeneralLinear.standardCongruencePoint ↥𝒪[F] F 1 B hBc
  have hy : (y : rationalPoints (GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))) =
      (GeneralLinear.rationalPointsEquiv n (CommRingCat.of F)).symm A := by
    apply (GeneralLinear.rationalPointsEquiv n (CommRingCat.of F)).injective
    rw [GeneralLinear.standardCongruencePoint_matrix, MulEquiv.apply_symm_apply, hB]
  exact hy ▸ y.property

/-- A single actual diagonal conjugation carries a compact unitriangular subgroup
into the standard model's level-one congruence subgroup. -/
theorem exists_rescale_mem_standardCongruence
    {Γ : Type v} [Group Γ] [TopologicalSpace Γ]
    (φ : Γ →* GL (Fin n) F) (hφ : Continuous φ)
    (hdiag : ∀ x i, (φ x : Matrix (Fin n) (Fin n) F) i i = 1)
    (hlow : ∀ x i j, j < i → (φ x : Matrix (Fin n) (Fin n) F) i j = 0)
    (K : Subgroup Γ) (hK : IsCompact (K : Set Γ)) :
    ∃ t : Fˣ, ∀ x ∈ K,
      (GeneralLinear.rationalPointsEquiv n (CommRingCat.of F)).symm (rescale t (φ x)) ∈
        (GeneralLinear.standardIntegralModel ↥𝒪[F] F (Fin n)).congruenceSubgroupAt 1 := by
  classical
  obtain ⟨t, ht⟩ := exists_rescale_strict_entries φ hφ hlow (K : Set Γ) hK
  have hd (x : Γ) (i : Fin n) :
      (rescale t (φ x) : Matrix (Fin n) (Fin n) F) i i = 1 := by
    rw [rescale_entry_of_le t (φ x) i i le_rfl, Nat.sub_self, pow_zero, mul_one, hdiag]
  have hb (x : Γ) (hx : x ∈ K) (i j : Fin n) :
      ValuativeRel.valuation F
        ((rescale t (φ x) : Matrix (Fin n) (Fin n) F) i j) ≤ 1 := by
    by_cases hij : i = j
    · subst j
      rw [hd, map_one]
    · exact (ht x hx i j hij).le
  refine ⟨t, fun x hx => mem_standardCongruence_of_entries _ (hb x hx) ?_ ?_⟩
  · intro i j
    rw [← map_inv, ← map_inv]
    exact hb x⁻¹ (K.inv_mem hx) i j
  · intro i j
    by_cases hij : i = j
    · subst j
      rw [hd, Matrix.one_apply_eq, sub_self, map_zero]
      exact zero_lt_one
    · rw [Matrix.one_apply_ne hij, sub_zero]
      exact ht x hx i j hij

end Congruence

end Langlands.GroupScheme.UnitriangularCongruence
