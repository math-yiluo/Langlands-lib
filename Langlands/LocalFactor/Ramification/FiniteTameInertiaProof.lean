import Langlands.LocalFactor.Ramification.FiniteTameInertia
import Langlands.LocalFactor.Ramification.InertiaSolvabilityProof
import Langlands.ClassFieldTheory.Local.PrimeRamificationArithmeticSupport
import Mathlib.RingTheory.IntegralDomain

/-!
# Finite tame inertia: proof
-/

noncomputable section

namespace Langlands.Ramification

open IsLocalRing

/-- Iterated `p`-powers of an element of the first lower group reach the
trivial group when the filtration terminates. -/
theorem isPGroup_lowerGroup_one_of_terminates {R G : Type*} [CommRing R] [IsLocalRing R]
    [Group G] [MulSemiringAction G R] {p : ℕ}
    (hpm : (p : R) ∈ maximalIdeal R) (hbot : ∃ b : ℕ, lowerGroup R G b = ⊥) :
    IsPGroup p (lowerGroup R G 1) := by
  intro x
  have h (k : ℕ) : (x : G) ^ p ^ k ∈ lowerGroup R G (k + 1) := by
    induction k with
    | zero => simpa only [pow_zero, pow_one] using x.2
    | succ k ih =>
      rw [pow_succ p, pow_mul]
      exact pow_mem_lowerGroup_succ_of_natCast_mem (by omega) hpm ih
  obtain ⟨b, hb⟩ := hbot
  have hx := lowerGroup_antitone R G (Nat.le_succ b) (h b)
  rw [hb] at hx
  exact ⟨b, Subtype.ext (Subgroup.mem_bot.mp hx)⟩

namespace Padic

universe uK uL

/-- The first lower group and the quotient of inertia by it have the
finite wild and tame structures of Serre, IV §2. -/
theorem finiteTameInertiaStructure : FiniteTameInertiaStructureStatement.{uK, uL} := by
  intro p _ K L _ _ _ _ T
  let G := L.Carrier ≃ₐ[K.Carrier] L.Carrier
  let R := T.Integers
  let := integerAction T K.Carrier
  let := T.residueCharP
  have hpm : (p : R) ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero T.ResidueField p
  obtain ⟨b, hb⟩ := exists_lowerRamificationGroup_eq_bot T K.Carrier
  have hwild : IsPGroup p (lowerGroup R G 1) :=
    isPGroup_lowerGroup_one_of_terminates hpm ⟨b, hb b le_rfl⟩
  have : IsDiscreteValuationRing R := by
    let := T.topology
    let := T.valuativeRel
    let := T.localField
    infer_instance
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let χ := uniformizerCharacter (G := G) hϖ.maximalIdeal_eq hϖ.ne_zero
  let χu := χ.toHomUnits
  have hker : χu.ker = finiteWildInInertia T K.Carrier := by
    ext x
    change χu x = 1 ↔ (x : G) ∈ lowerGroup R G 1
    constructor
    · intro hx
      have hfrob : ∀ y : R, ∃ z : R, y - z ^ p ∈ maximalIdeal R := by
        have := T.finite_residueField
        intro y
        obtain ⟨c, hc⟩ := surjective_frobenius T.ResidueField p (residue R y)
        obtain ⟨z, rfl⟩ := residue_surjective c
        refine ⟨z, ?_⟩
        rw [← residue_eq_zero_iff, map_sub, map_pow, sub_eq_zero, ← hc, frobenius_def]
      have hχ : χ x = 1 := congrArg Units.val hx
      exact mem_lowerGroup_one_of_frobenius hϖ.maximalIdeal_eq Fact.out hpm hfrob x.2
        (smul_uniformizer_sub_mem_of_eq_one hϖ.maximalIdeal_eq hϖ.ne_zero hχ)
    · intro hx
      obtain ⟨k, hk⟩ := hwild (⟨x.1, hx⟩ : lowerGroup R G 1)
      have hxpow : x ^ p ^ k = 1 :=
        Subtype.ext (congrArg (fun y : lowerGroup R G 1 => (y : G)) hk)
      have hχpow : χ x ^ p ^ k = 1 := by rw [← map_pow, hxpow, map_one]
      apply Units.ext
      change χ x = 1
      apply sub_eq_zero.mp
      apply (pow_eq_zero_iff (pow_ne_zero k (Fact.out : p.Prime).ne_zero)).mp
      rw [sub_pow_char_pow, one_pow, hχpow, sub_self]
  let e : finiteTameInertiaQuotient T K.Carrier ≃* (lowerGroup R G 0 ⧸ χu.ker) :=
    @QuotientGroup.quotientMulEquivOfEq _ _ (finiteWildInInertia T K.Carrier) χu.ker
      inferInstance χu.normal_ker hker.symm
  let θ := (QuotientGroup.kerLift χu).comp e.toMonoidHom
  have hθ : Function.Injective θ := (QuotientGroup.kerLift_injective χu).comp e.injective
  have hcyc := isCyclic_of_injective_ringHom ((Units.coeHom T.ResidueField).comp θ)
    (Units.val_injective.comp hθ)
  have hdvd := Subgroup.card_dvd_of_injective θ hθ
  rw [Nat.card_units] at hdvd
  change Nat.card (finiteTameInertiaQuotient T K.Carrier) ∣ T.residueCardinality - 1 at hdvd
  refine ⟨hwild, ⟨θ, hθ⟩, hcyc, hdvd, (Fact.out : p.Prime).coprime_iff_not_dvd.mpr ?_⟩
  intro h
  have hz : p ∣ T.residueCardinality := by
    rw [T.residueCardinality_eq_pow]
    exact dvd_pow_self p T.residueDegree_pos.ne'
  have h1 := Nat.dvd_sub hz (h.trans hdvd)
  rw [Nat.sub_sub_self T.residueCardinality_gt_one.le] at h1
  exact (Fact.out : p.Prime).not_dvd_one h1

end Padic

end Langlands.Ramification
