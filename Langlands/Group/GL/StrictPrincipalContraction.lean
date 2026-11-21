import Langlands.Group.GL.BlockIwahoriDefinitions
import Langlands.Representation.Conductor.SphericalCyclicity.Parahoric

/-! # One-step contraction of principal congruence radicals -/

namespace Langlands.GeneralLinear.BlockShape

open Conductor Conductor.SphericalCyclicity

universe u

variable {k : Type u} [Field k] [ValuativeRel k] {r : ℕ}
  (B : BlockShape (r + 1)) {π : kˣ}
  (hπ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation k) π)

local notation "v" => ValuativeRel.valuation k
local notation "G" => GeneralLinear (r + 1) k
local notation "J" => principalLevelSubgroup k r
local notation "𝟙" => (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) k)

private theorem conj_level_entry_bound (a : Fin B.length → kˣ) {d : ℕ} {g : G}
    (hg : ∀ i j, v (g i j - 𝟙 i j) ≤ v (π : k) ^ d)
    (hdiag : ∀ i x y, g (B.index i x) (B.index i y) = if x = y then 1 else 0)
    (hratio : ∀ i j x y, i ≠ j → g (B.index i x) (B.index j y) ≠ 0 →
      v ((a i * (a j)⁻¹ : kˣ) : k) ≤ v (π : k)) (x y : Fin (r + 1)) :
    v ((B.blockScalar k a * g * (B.blockScalar k a)⁻¹) x y - 𝟙 x y) ≤ v (π : k) ^ (d + 1) := by
  obtain ⟨⟨i, x⟩, rfl⟩ := B.indexEquiv.surjective x
  obtain ⟨⟨j, y⟩, rfl⟩ := B.indexEquiv.surjective y
  change v ((B.blockScalar k a * g * (B.blockScalar k a)⁻¹)
    (B.index i x) (B.index j y) - 𝟙 (B.index i x) (B.index j y)) ≤ _
  rw [B.blockScalar_conj_apply]
  by_cases h : i = j
  · subst j
    simp only [mul_inv_cancel, Units.val_one, one_mul, hdiag, Matrix.one_apply, (B.index i).injective.eq_iff,
      sub_self, map_zero]
    exact zero_le
  · have hne : B.index i x ≠ B.index j y := fun e =>
      h (congrArg Sigma.fst (B.indexEquiv.injective e))
    rw [Matrix.one_apply, ite_eq_right hne, sub_zero]
    by_cases hzero : g (B.index i x) (B.index j y) = 0
    · rw [hzero, mul_zero, map_zero]
      exact zero_le
    have hentry : v (g (B.index i x) (B.index j y)) ≤ v (π : k) ^ d := by
      simpa only [Matrix.one_apply, ite_eq_right hne, sub_zero] using hg (B.index i x) (B.index j y)
    rw [map_mul, pow_succ']
    exact mul_le_mul' (hratio i j x y h hzero) hentry

include hπ in
private theorem conj_mem_principalLevel_succ (a : Fin B.length → kˣ) (H : Subgroup G)
    (hdiag : ∀ g ∈ H, ∀ i x y, g (B.index i x) (B.index i y) = if x = y then 1 else 0)
    (hratio : ∀ g ∈ H, ∀ i j x y, i ≠ j → g (B.index i x) (B.index j y) ≠ 0 →
      v ((a i * (a j)⁻¹ : kˣ) : k) ≤ v (π : k)) {d : ℕ} {g : G} (hg : g ∈ J d ⊓ H) :
    B.blockScalar k a * g * (B.blockScalar k a)⁻¹ ∈ J (d + 1) := by
  obtain ⟨h1, h2⟩ := (mem_principalLevelSubgroup_iff hπ g).mp hg.1
  have hi := H.inv_mem hg.2
  refine (mem_principalLevelSubgroup_iff hπ _).mpr
    ⟨B.conj_level_entry_bound a h1 (hdiag g hg.2) (hratio g hg.2), ?_⟩
  simpa only [mul_inv_rev, inv_inv, mul_assoc] using
    B.conj_level_entry_bound a h2 (hdiag g⁻¹ hi) (hratio g⁻¹ hi)

include hπ in
/-- If all positive root ratios lie in the maximal ideal, conjugation improves
the upper radical principal congruence by one level. -/
theorem upper_conj_mem_principalLevel_succ (a : Fin B.length → kˣ)
    (ha : ∀ i j, i < j → v ((a i * (a j)⁻¹ : kˣ) : k) ≤ v (π : k)) {d : ℕ}
    {g : G} (hg : g ∈ J d ⊓ B.unipotentSubgroup k) :
    B.blockScalar k a * g * (B.blockScalar k a)⁻¹ ∈ J (d + 1) := by
  refine B.conj_mem_principalLevel_succ hπ a (B.unipotentSubgroup k) (fun x hx =>
    ((B.mem_unipotentSubgroup_iff k x).mp hx).2) ?_ hg
  intro x hx i j u w hne hnz
  apply ha
  apply lt_of_le_of_ne _ hne
  exact le_of_not_gt fun hji => hnz
    ((B.mem_parabolic_iff k x).mp ((B.mem_unipotentSubgroup_iff k x).mp hx).1 i j u w hji)

include hπ in
/-- Under the same ratio bounds, inverse conjugation improves the opposite
radical principal congruence by one level. -/
theorem lower_inv_conj_mem_principalLevel_succ (a : Fin B.length → kˣ)
    (ha : ∀ i j, i < j → v ((a i * (a j)⁻¹ : kˣ) : k) ≤ v (π : k)) {d : ℕ}
    {g : G} (hg : g ∈ J d ⊓ B.oppositeUnipotentSubgroup k) :
    (B.blockScalar k a)⁻¹ * g * B.blockScalar k a ∈ J (d + 1) := by
  have hratio : ∀ x ∈ B.oppositeUnipotentSubgroup k, ∀ i j u w,
      i ≠ j → x (B.index i u) (B.index j w) ≠ 0 →
      v (((a⁻¹ i) * (a⁻¹ j)⁻¹ : kˣ) : k) ≤ v (π : k) := by
    intro x hx i j u w hne hnz
    have hji : j < i := lt_of_le_of_ne (le_of_not_gt fun hij => hnz
      ((B.mem_oppositeParabolic_iff k x).mp
        ((B.mem_oppositeUnipotentSubgroup_iff k x).mp hx).1 i j u w hij)) hne.symm
    simpa only [Pi.inv_apply, inv_inv, mul_comm] using ha j i hji
  simpa only [B.blockScalar_inv, inv_inv] using
    (B.conj_mem_principalLevel_succ hπ a⁻¹ (B.oppositeUnipotentSubgroup k)
      (fun x hx => ((B.mem_oppositeUnipotentSubgroup_iff k x).mp hx).2) hratio hg)

/-- One-step contraction in the two opposite principal congruence radicals. -/
def StrictPrincipalContractionStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] (r : ℕ) (B : BlockShape (r + 1))
    (π : kˣ) (_ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation k) π)
    (a : Fin B.length → kˣ),
    (∀ i j, i < j →
      ValuativeRel.valuation k ((a i * (a j)⁻¹ : kˣ) : k) ≤ ValuativeRel.valuation k (π : k)) →
    ∀ (d : ℕ) (g : GeneralLinear (r + 1) k),
    (g ∈ principalLevelSubgroup k r d ⊓ B.unipotentSubgroup k →
      B.blockScalar k a * g * (B.blockScalar k a)⁻¹ ∈ principalLevelSubgroup k r (d + 1)) ∧
    (g ∈ principalLevelSubgroup k r d ⊓ B.oppositeUnipotentSubgroup k →
      (B.blockScalar k a)⁻¹ * g * B.blockScalar k a ∈ principalLevelSubgroup k r (d + 1))

theorem strictPrincipalContraction : StrictPrincipalContractionStatement.{u} :=
  fun _ _ _ _ B _ hπ a ha _ _ =>
    ⟨B.upper_conj_mem_principalLevel_succ hπ a ha, B.lower_inv_conj_mem_principalLevel_succ hπ a ha⟩

end Langlands.GeneralLinear.BlockShape
