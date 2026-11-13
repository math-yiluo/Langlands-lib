import Langlands.Geometry.Building.ApartmentQuotientComparison
import Mathlib.Tactic.Group

/-! # Common apartments and two-point subgroup factorization -/

namespace Langlands.Geometry.Building.ApartmentQuotient

universe uH uA

variable {H : Type uH} [Group H] {N : Subgroup H}
  {A : Type uA} [MulAction N A] (P : CovariantSubgroupFamily N A)

/-- A common translated apartment for a base point and a translated base point
is equivalent to the corresponding two-point subgroup factorization. -/
theorem exists_common_apartment_iff_factorization (x y : A) (g : H) :
    (∃ (h : H) (a b : A),
      h • apartment P a = apartment P x ∧ h • apartment P b = g • apartment P y) ↔
    ∃ p ∈ P x, ∃ n : N, ∃ q ∈ P y, g = p * (n : H) * q := by
  constructor
  · rintro ⟨h, a, b, ha, hb⟩
    have ha' : mk P (1, x) = mk P (h, a) := by
      simpa only [apartment, smul_mk, mul_one] using ha.symm
    have hb' : mk P (g, y) = mk P (h, b) := by
      simpa only [apartment, smul_mk, mul_one] using hb.symm
    obtain ⟨n, -, hn⟩ := (mk_eq_mk_iff P 1 h x a).mp ha'
    obtain ⟨m, -, hm⟩ := (mk_eq_mk_iff P g h y b).mp hb'
    have hp : h * (n : H) ∈ P x := by
      simpa only [inv_one, one_mul] using hn
    refine ⟨h * (n : H), hp, n⁻¹ * m, (g⁻¹ * h * (m : H))⁻¹, inv_mem hm, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  · rintro ⟨p, hp, n, q, hq, rfl⟩
    have hpx : p • apartment P x = apartment P x :=
      MulAction.mem_stabilizer_iff.mp (le_stabilizer_apartment P x hp)
    have hqy : q • apartment P y = apartment P y :=
      MulAction.mem_stabilizer_iff.mp (le_stabilizer_apartment P y hq)
    refine ⟨p, x, n • y, hpx, ?_⟩
    rw [apartment_smul, mul_smul, mul_smul, hqy]

/-- Common translated apartments for the whole original quotient are exactly
the family of two-point subgroup factorizations. -/
theorem hasCommonTranslatedApartment_iff_factorization :
    HasCommonTranslatedApartment P ↔
      ∀ (x y : A) (g : H), ∃ p ∈ P x, ∃ n : N, ∃ q ∈ P y,
        g = p * (n : H) * q := by
  constructor
  · intro hcommon x y g
    exact (exists_common_apartment_iff_factorization P x y g).mp
      (hcommon (apartment P x) (g • apartment P y))
  · intro hfactor q q'
    obtain ⟨g, x, rfl⟩ := exists_smul_apartment P q
    obtain ⟨h, y, rfl⟩ := exists_smul_apartment P q'
    obtain ⟨p, a, b, ha, hb⟩ :=
      (exists_common_apartment_iff_factorization P x y (g⁻¹ * h)).mpr (hfactor x y _)
    refine ⟨g * p, a, b, ?_, ?_⟩
    · rw [mul_smul, ha]
    · rw [mul_smul, hb, mul_smul, smul_inv_smul]

/-- The exact algebraic criterion for common translated apartments, with no
restriction on the group or the two universes. -/
def CommonApartmentFactorizationStatement : Prop :=
  ∀ (H : Type uH) [Group H] (N : Subgroup H)
    (A : Type uA) [MulAction N A] (P : CovariantSubgroupFamily N A),
    HasCommonTranslatedApartment P ↔
      ∀ (x y : A) (g : H), ∃ p ∈ P x, ∃ n : N, ∃ q ∈ P y,
        g = p * (n : H) * q

/-- Common translated apartments are equivalent to two-point subgroup
factorization. -/
theorem commonApartmentFactorization :
    CommonApartmentFactorizationStatement.{uH, uA} := by
  intro H _ N A _ P
  exact hasCommonTranslatedApartment_iff_factorization P

end Langlands.Geometry.Building.ApartmentQuotient
