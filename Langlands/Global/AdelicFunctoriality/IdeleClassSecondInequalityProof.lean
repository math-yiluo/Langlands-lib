import Langlands.Global.AdelicFunctoriality.IdeleClassSecondInequalityStatement
import Langlands.Global.AdelicFunctoriality.IdeleClassNormTowerProof
import Langlands.Global.AdelicFunctoriality.IdeleClassNormIndexFiniteProof
import Langlands.Global.AdelicFunctoriality.IdeleClassPrimeDegreeSecondInequalityProof
import Langlands.Global.AdelicFunctoriality.CyclotomicSecondInequalityReduction
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.Nilpotent

/-! # The second inequality for actual idele classes

Normal subgroups of order `p` reduce the p-group case to prime degree.
Sylow fixed fields and the degree-power bound give the general Galois case.
-/

noncomputable section

universe u v

namespace Langlands.Global.AdelicFunctoriality
namespace SecondInequalityProof

/-- The numerical conclusion of the Sylow argument, with its prime-to-p factor exposed. -/
theorem dvd_of_primewise_coprime_factor {d n : ℕ}
    (h : ∀ p : ℕ, Nat.Prime p → ∃ a b : ℕ,
      Nat.Coprime p a ∧ d ∣ a * b ∧ b ∣ n) : d ∣ n := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd n d).mpr
  intro p k hp hpk
  obtain ⟨a, b, ha, hd, hb⟩ := h p hp
  exact dvd_trans ((ha.pow_left k).dvd_mul_left.mp (dvd_trans hpk hd)) hb

open NumberField
open scoped NumberField

/-- Conditional prime-power reduction, with a fixed base field. -/
theorem ideleClassNorm_index_dvd_of_isPGroup
    (K : Type u) [Field K] [NumberField K]
    (htower : ∀ (E L : Type v) [Field E] [NumberField E] [Field L] [NumberField L]
      [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L],
      ∀ x : IdeleClassGroup (𝓞 L) L,
        ideleClassNorm (K := K) (L := L) x =
          ideleClassNorm (K := K) (L := E) (ideleClassNorm (K := E) (L := L) x))
    (hbound : ∀ (L : Type v) [Field L] [NumberField L] [Algebra K L],
      ∃ r : ℕ, (ideleClassNorm (K := K) (L := L)).toMonoidHom.range.index ∣
        Module.finrank K L ^ r)
    (hprime : ∀ (E L : Type v) [Field E] [NumberField E] [Field L] [NumberField L]
      [Algebra E L] [IsGalois E L], Nat.Prime (Module.finrank E L) →
        (ideleClassNorm (K := E) (L := L)).toMonoidHom.range.index ∣ Module.finrank E L)
    (L : Type v) [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (p : ℕ) [Fact p.Prime] (hp : IsPGroup p Gal(L/K)) :
    (ideleClassNorm (K := K) (L := L)).toMonoidHom.range.index ∣ Module.finrank K L := by
  induction hn : Module.finrank K L using Nat.strong_induction_on generalizing L with
  | h n ih =>
    by_cases hn1 : n = 1
    · obtain ⟨r, hr⟩ := hbound L
      simpa [hn, hn1] using hr
    · have hpdvd : p ∣ Nat.card Gal(L/K) :=
        hp.card_eq_or_dvd.resolve_left (by rwa [IsGalois.card_aut_eq_finrank, hn])
      let : Group.IsNilpotent Gal(L/K) := hp.isNilpotent
      obtain ⟨H, hcard, hnormal⟩ :=
        Group.IsNilpotent.exists_normal_card_eq_of_dvd_card hpdvd
      let : H.Normal := hnormal
      let E : IntermediateField K L := IntermediateField.fixedField H
      have hEL : Module.finrank E L = p :=
        (IntermediateField.finrank_fixedField_eq_card H).trans hcard
      have hpE : IsPGroup p Gal(E/K) :=
        (hp.to_quotient H).of_equiv (IsGalois.normalAutEquivQuotient H)
      have hdeg : Module.finrank K E * p = n := by
        rw [← hEL, Module.finrank_mul_finrank, hn]
      have hlt : Module.finrank K E < n := by
        rw [← hdeg]
        exact lt_mul_right Module.finrank_pos (Fact.out : Nat.Prime p).one_lt
      have hKE := ih (Module.finrank K E) hlt E hpE rfl
      have hELindex := hprime E L (hEL ▸ (Fact.out : Nat.Prime p))
      have hidx := ideleClassNorm_range_index_dvd_mul_of_tower K E L (htower E L)
      exact dvd_trans hidx (by
        simpa [Module.finrank_mul_finrank, hn] using mul_dvd_mul hKE hELindex)

/-- The general Sylow step, conditional on the prime-power cases. -/
theorem ideleClassNorm_index_dvd_of_sylow_cases
    (K : Type u) (L : Type v) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (htower : ∀ E : IntermediateField K L, ∀ x : IdeleClassGroup (𝓞 L) L,
      ideleClassNorm (K := K) (L := L) x =
        ideleClassNorm (K := K) (L := E) (ideleClassNorm (K := E) (L := L) x))
    (hbound : ∀ E : IntermediateField K L, ∃ r : ℕ,
      (ideleClassNorm (K := K) (L := E)).toMonoidHom.range.index ∣ Module.finrank K E ^ r)
    (hpgroup : ∀ (E : IntermediateField K L) (p : ℕ) [Fact p.Prime],
      IsPGroup p Gal(L/E) →
        (ideleClassNorm (K := E) (L := L)).toMonoidHom.range.index ∣ Module.finrank E L) :
    (ideleClassNorm (K := K) (L := L)).toMonoidHom.range.index ∣ Module.finrank K L := by
  apply dvd_of_primewise_coprime_factor
  intro p hp
  let : Fact p.Prime := ⟨hp⟩
  let P : Sylow p Gal(L/K) := Classical.arbitrary _
  let E : IntermediateField K L := IntermediateField.fixedField P.toSubgroup
  obtain ⟨r, hr⟩ := hbound E
  have hcop : Nat.Coprime p (Module.finrank K E) := by
    apply hp.coprime_iff_not_dvd.mpr
    rw [IntermediateField.finrank_eq_fixingSubgroup_index,
      IntermediateField.fixingSubgroup_fixedField]
    exact P.not_dvd_index
  have hpE : IsPGroup p Gal(L/E) :=
    P.isPGroup'.of_equiv (IntermediateField.subgroupEquivAlgEquiv P.toSubgroup)
  refine ⟨Module.finrank K E ^ r, Module.finrank E L, hcop.pow_right r, ?_, ?_⟩
  · exact dvd_trans (ideleClassNorm_range_index_dvd_mul_of_tower K E L (htower E))
      (mul_dvd_mul hr (hpgroup E p hpE))
  · rw [← Module.finrank_mul_finrank K E L]
    exact dvd_mul_left _ _

/-- Assemble the general inequality from norm towers, degree-power bounds and prime degrees. -/
theorem secondInequality_of_inputs
    (htowerLow : IdeleClassNormTower.{u, v, v})
    (htowerHigh : IdeleClassNormTower.{v, v, v})
    (hboundLow : IdeleClassNormIndexFinite.{u, v})
    (hboundHigh : IdeleClassNormIndexFinite.{v, v})
    (hprime : IdeleClassPrimeDegreeSecondInequality.{v, v}) :
    IdeleClassSecondInequality.{u, v} := by
  intro K _ _ L _ _ _ _
  apply ideleClassNorm_index_dvd_of_sylow_cases K L
  · intro E
    exact htowerLow K E L
  · intro E
    exact (hboundLow K E).2
  · intro E p _ hp
    apply ideleClassNorm_index_dvd_of_isPGroup E ?_ ?_ ?_ L p hp
    · intro F M _ _ _ _ _ _ _ _
      exact htowerHigh E F M
    · intro M _ _ _
      exact (hboundHigh E M).2
    · intro F M _ _ _ _ _ _
      exact hprime F M

end SecondInequalityProof

/-- The actual idele-class norm index divides the degree of every Galois
extension of number fields. -/
theorem ideleClassSecondInequality : IdeleClassSecondInequality.{u, v} :=
  SecondInequalityProof.secondInequality_of_inputs
    ideleClassNormTower.{u, v, v} ideleClassNormTower.{v, v, v}
    ideleClassNormIndexFinite.{u, v} ideleClassNormIndexFinite.{v, v}
    ideleClassPrimeDegreeSecondInequality.{v, v}

end Langlands.Global.AdelicFunctoriality
