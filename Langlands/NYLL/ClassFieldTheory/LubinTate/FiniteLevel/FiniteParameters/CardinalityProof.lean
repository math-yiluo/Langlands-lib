/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 441, 2026-11-14: prove the published M358.008 target
(FiniteParameters.lean, lines 116–167) of upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 with the Langlands.NYLL prefix.
The source proof through the principal-unit filtration is replaced by a direct
Mathlib proof through the finite quotient ring O ⧸ m ^ (n + 1); see the paired
Markdown. The retained license and notices are in licenses/NYLL/.
-/
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameters.CardinalityStatements
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Valuation.Discrete.Basic

/-!
# Cardinality of the finite unit parameter quotient

The only theorem proves NYLL M358.008 as its exact published target.
-/

noncomputable section
universe u v
namespace Langlands.NYLL.LubinTate
open LocalFieldTheory.DiscreteValuationField
variable {K : Type u} [Field K]

/-- M358.008: the finite unit parameter quotient at primitive level `n + 1`
has `(q - 1) * q ^ n` elements, where `q` is the residue-field cardinality. -/
theorem standardLubinTateUnitParameter_natCard
    (F : LocalField.{u, v} K) (n : ℕ) :
    standardLubinTateUnitParameter_natCardStatement F n := by
  -- The ideal `m ^ (n + 1)` of the valuation ring and the unit map to its quotient.
  let I : Ideal F.valuationSubring := F.maximalIdeal ^ (n + 1)
  have hIm : I ≤ F.maximalIdeal := Ideal.pow_le_self (Nat.succ_ne_zero n)
  have hm_ne_top : F.maximalIdeal ≠ ⊤ := Ideal.IsMaximal.ne_top inferInstance
  let J : Ideal (F.valuationSubring ⧸ I) := F.maximalIdeal.map (Ideal.Quotient.mk I)
  have hmemJ : ∀ a : F.valuationSubring,
      Ideal.Quotient.mk I a ∈ J ↔ a ∈ F.maximalIdeal := fun a =>
    Ideal.mem_quotient_iff_mem hIm
  -- A residue class modulo `m ^ (n + 1)` is a unit iff its representative is.
  have hunit : ∀ a : F.valuationSubring,
      IsUnit (Ideal.Quotient.mk I a) ↔ a ∉ F.maximalIdeal := by
    intro a
    constructor
    · intro ha hmem
      have hJ : J = ⊤ := Ideal.eq_top_of_isUnit_mem J ((hmemJ a).mpr hmem) ha
      have h1 : Ideal.Quotient.mk I (1 : F.valuationSubring) ∈ J := by
        rw [hJ]; exact Submodule.mem_top
      exact hm_ne_top ((Ideal.eq_top_iff_one _).mpr ((hmemJ 1).mp h1))
    · intro ha
      exact (IsLocalRing.notMem_maximalIdeal.mp ha).map (Ideal.Quotient.mk I)
  let φ : F.valuationSubringˣ →* (F.valuationSubring ⧸ I)ˣ :=
    Units.map (Ideal.Quotient.mk I).toMonoidHom
  have hker : φ.ker = CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1) := by
    ext x
    rw [MonoidHom.mem_ker, Units.ext_iff]
    exact Ideal.Quotient.eq
  have hsurj : Function.Surjective φ := by
    intro r
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (r : F.valuationSubring ⧸ I)
    have hau : IsUnit a :=
      IsLocalRing.notMem_maximalIdeal.mp ((hunit a).mp (ha ▸ r.isUnit))
    refine ⟨hau.unit, Units.ext ?_⟩
    exact ha
  -- Cardinalities of the residue field and of `O ⧸ m ^ (n + 1)`.
  set q := Nat.card F.residueField with hq_def
  have hq_pos : 0 < q := Nat.card_pos
  have hm_ne_bot : F.maximalIdeal ≠ ⊥ :=
    IsDiscreteValuationRing.not_a_field F.valuationSubring
  have hcardR : Nat.card (F.valuationSubring ⧸ I) = q ^ (n + 1) := by
    have h := cardQuot_pow_of_prime (S := F.valuationSubring) (P := F.maximalIdeal)
      hm_ne_bot (i := n + 1)
    rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply] at h
    exact h
  have : Finite (F.valuationSubring ⧸ I) :=
    Nat.finite_of_card_ne_zero (by rw [hcardR]; exact (pow_pos hq_pos _).ne')
  -- The image of `m` has `q ^ n` elements.
  have hcardJ : Nat.card J = q ^ n := by
    have h := AddSubgroup.card_mul_index J.toAddSubgroup
    have hidx : J.toAddSubgroup.index = q := by
      change Submodule.cardQuot J = q
      rw [Submodule.cardQuot_apply]
      exact Nat.card_congr (DoubleQuot.quotQuotEquivQuotOfLE hIm).toEquiv
    rw [hidx, hcardR, pow_succ] at h
    exact Nat.eq_of_mul_eq_mul_right hq_pos h
  -- The units of `O ⧸ m ^ (n + 1)` are the complement of the image of `m`.
  have hunits : Nat.card (F.valuationSubring ⧸ I)ˣ = q ^ (n + 1) - q ^ n := by
    have hrange : Set.range (Units.val : (F.valuationSubring ⧸ I)ˣ → _) =
        (J : Set (F.valuationSubring ⧸ I))ᶜ := by
      ext x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      change IsUnit (Ideal.Quotient.mk I a) ↔ Ideal.Quotient.mk I a ∉ J
      rw [hunit a, hmemJ a]
    rw [← Nat.card_range_of_injective Units.val_injective, hrange,
      Nat.card_coe_set_eq]
    have h := Set.ncard_add_ncard_compl (J : Set (F.valuationSubring ⧸ I))
    rw [← Nat.card_coe_set_eq (J : Set (F.valuationSubring ⧸ I))] at h
    change Nat.card J + _ = _ at h
    omega
  -- Assemble.
  change Nat.card (F.valuationSubringˣ ⧸
      CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)) = (q - 1) * q ^ n
  rw [← hker, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hsurj).toEquiv,
    hunits, Nat.sub_mul, one_mul, pow_succ, mul_comm]

end Langlands.NYLL.LubinTate
