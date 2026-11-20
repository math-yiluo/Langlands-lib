import Langlands.Geometry.FormalGroup.FieldRationalDegree
import Langlands.Geometry.FormalGroup.GlobalRationalHeight

/-! # Recovering an actual kernel-rank height from a field-valued degree -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

variable {O : Type u} [CommRing O] {π : O}
variable {k F : Type v} [Field k] [Field F] [Algebra O k] [Algebra O F]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O k σ} {N : ModuleLaw O k τ}
variable {q H : ℕ} {i : ℤ}

namespace RationalHom.ScalarIsogenyPresentation

/-- The scalar height identifies the denominator in the rank ratio. -/
theorem degree_eq_div_scalarHeight {z : RationalHom F M N} (P : ScalarIsogenyPresentation π z)
    (hM : M.HasPiHeight π q H) :
    P.degree hM.piDivisible = (P.isIsogeny.fieldDegree : ℚ) / (q : ℚ) ^ (P.exponent * H) := by
  rw [degree, Hom.IsIsogeny.fieldDegree_eq_of_rank _ (hM.scalarPower_rank P.exponent),
    Nat.cast_pow]

/-- A degree equal to an integer power of `q` gives a ranked presentation with the same exponent
as signed height. -/
def globalHeight_of_degree_zpow {z : RationalHom F M N}
    (P : ScalarIsogenyPresentation π z) (hq : 1 < q) (hM : M.HasPiHeight π q H)
    (hi : P.degree hM.piDivisible = (q : ℚ) ^ i) :
    { Q : GlobalHeightPresentation π q z // Q.index H = i } := by
  have hq' : (1 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have hq0 : (q : ℚ) ≠ 0 := (lt_trans zero_lt_one hq').ne'
  let j : ℤ := i + ((P.exponent * H : ℕ) : ℤ)
  have hr : (P.isIsogeny.fieldDegree : ℚ) = (q : ℚ) ^ j := by
    rw [P.degree_eq_div_scalarHeight hM] at hi
    change (P.isIsogeny.fieldDegree : ℚ) = (q : ℚ) ^ (i + ((P.exponent * H : ℕ) : ℤ))
    rw [zpow_add₀ hq0, zpow_natCast]
    exact (div_eq_iff (pow_ne_zero _ hq0)).mp hi
  have hj : 0 ≤ j := (one_le_zpow_iff_right₀ hq').mp (by
    rw [← hr]
    exact_mod_cast P.isIsogeny.fieldDegree_pos)
  have hcast := Int.toNat_of_nonneg hj
  have hr' : P.isIsogeny.fieldDegree = q ^ j.toNat := by
    rw [← hcast, zpow_natCast] at hr
    exact_mod_cast hr
  let Q : GlobalHeightPresentation π q z :=
    ⟨P, j.toNat, hr' ▸ P.isIsogeny.hasKernelRank_fieldDegree⟩
  refine ⟨Q, ?_⟩
  change (j.toNat : ℤ) - (P.exponent : ℤ) * H = i
  rw [hcast]
  change i + ((P.exponent * H : ℕ) : ℤ) - (P.exponent : ℤ) * H = i
  rw [Nat.cast_mul, add_sub_cancel_right]

end RationalHom.ScalarIsogenyPresentation

namespace QuasiIsogeny

variable [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O F]

/-- Promote a field-valued degree calculation to a global presentation by the actual kernel. -/
theorem exists_globalHeight_of_fieldDegree_zpow (e : QuasiIsogeny F M N)
    (hπ : Irreducible π) (hq : 1 < q) (hM : M.HasPiHeight π q H) (hN : N.IsPiDivisible π)
    (hi : e.fieldDegree hπ hM.piDivisible hN = (q : ℚ) ^ i) :
    ∃ P : RationalHom.GlobalHeightPresentation π q e.hom, P.index H = i := by
  let P := (e.scalarIsogenyPresentation hπ hM.piDivisible hN).globalHeight_of_degree_zpow hq hM hi
  exact ⟨P.val, P.property⟩

end QuasiIsogeny

end Langlands.FormalGroup.ModuleLaw
