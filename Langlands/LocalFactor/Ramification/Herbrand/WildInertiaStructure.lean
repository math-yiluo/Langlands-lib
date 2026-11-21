import Langlands.LocalFactor.Ramification.Herbrand.LastGroupProof
import Langlands.LocalFactor.Ramification.InertiaSolvabilityProof
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.GroupTheory.Index

/-! # Tame inertia quotient and mixed-depth ramification commutators -/

noncomputable section

namespace Langlands.Ramification.HerbrandBridge

open IsLocalRing _root_.Langlands.Ramification.Padic

universe uK uL

section MixedDepth

variable {A : Type*} [CommRing A] [IsLocalRing A]

/-- Automorphisms at possibly different lower depths commute modulo the
maximal-ideal power for the sum of the depths. -/
theorem commutator_sub_mem_maximalIdeal_pow_add (f g : A ≃+* A) {i j : ℕ}
    (hf : ∀ x, f x - x ∈ maximalIdeal A ^ (i + 1))
    (hg : ∀ x, g x - x ∈ maximalIdeal A ^ (j + 1)) (x : A) :
    f (g x) - g (f x) ∈ maximalIdeal A ^ (i + j + 1) := by
  have h1 := sub_mem_maximalIdeal_pow_of_mem f hf (j + 1) (by omega) (g x - x) (hg x)
  have h2 := sub_mem_maximalIdeal_pow_of_mem g hg (i + 1) (by omega) (f x - x) (hf x)
  have h : f (g x) - g (f x) =
      (f (g x - x) - (g x - x)) - (g (f x - x) - (f x - x)) := by
    rw [map_sub, map_sub]
    ring
  rw [show j + 1 + i = i + j + 1 by omega] at h1
  rw [show i + 1 + j = i + j + 1 by omega] at h2
  rw [h]
  exact Ideal.sub_mem _ h1 h2

end MixedDepth

variable {p : ℕ} [Fact p.Prime] {L : PadicField.{uL} p} (T : L.TopologicalData)
  (K : Type uK) [Field K] [Algebra (Padic p) K] [Algebra K L.Carrier]
  [IsScalarTower (Padic p) K L.Carrier]

/-- For automorphisms at lower depths `i` and `j`, their commutator is at
lower depth `i + j`. -/
theorem commutator_mem_lowerRamificationGroup_add {i j : ℕ} {σ τ : L.Carrier ≃ₐ[K] L.Carrier}
    (hσ : σ ∈ lowerRamificationGroup T K i) (hτ : τ ∈ lowerRamificationGroup T K j) :
    (τ * σ)⁻¹ * (σ * τ) ∈ lowerRamificationGroup T K (i + j) := by
  rw [Padic.mem_lowerRamificationGroup] at hσ hτ ⊢
  intro x
  have hc := commutator_sub_mem_maximalIdeal_pow_add (integerAutomorphism T K σ)
    (integerAutomorphism T K τ) hσ hτ x
  set e := integerAutomorphism T K (τ * σ)⁻¹
  have he := (ringEquiv_mem_maximalIdeal_pow_iff e (i + j + 1) _).mpr hc
  rw [map_sub] at he
  rw [integerAutomorphism_mul, integerAutomorphism_mul]
  convert he using 2
  rw [← integerAutomorphism_mul T K τ σ x]
  exact (integerAutomorphism_inv_apply T K (τ * σ) x).symm

/-- The commutator of wild inertia and a group of positive upper depth `a`
is in a group of strictly larger upper depth. -/
theorem exists_gt_commutator_mem_upperRamificationGroup_of_wild {a : ℝ} (ha : 0 < a)
    {σ τ : L.Carrier ≃ₐ[K] L.Carrier}
    (hσ : σ ∈ lowerRamificationGroup T K 1) (hτ : τ ∈ upperRamificationGroup T K a) :
    ∃ w, a < w ∧ (τ * σ)⁻¹ * (σ * τ) ∈ upperRamificationGroup T K w := by
  have hpos : 0 < herbrandPsi T K a := herbrandPsi_pos T K ha
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ⌈herbrandPsi T K a⌉ = (m : ℤ) :=
    ⟨_, (Int.toNat_of_nonneg (Int.ceil_nonneg hpos.le)).symm⟩
  have hle : herbrandPsi T K a ≤ (m : ℝ) := by
    have hh := Int.le_ceil (herbrandPsi T K a)
    rw [hm, Int.cast_natCast] at hh
    exact hh
  have ht : τ ∈ lowerRamificationGroup T K m := by
    rw [Padic.upperRamificationGroup_eq_lower, hm, ← Padic.lowerRamificationGroupReal_int,
      Int.cast_natCast, Padic.lowerRamificationGroupReal_nat] at hτ
    exact hτ
  have hdepth : herbrandPsi T K a < ((m + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  refine ⟨herbrandPhi T K ((m + 1 : ℕ) : ℝ), ?_, ?_⟩
  · have h := herbrandPhi_strictMono T K hdepth
    rwa [Padic.herbrandPhi_herbrandPsi] at h
  · rw [Padic.upperRamificationGroup_phi, Padic.lowerRamificationGroupReal_nat]
    simpa only [Nat.add_comm 1 m] using commutator_mem_lowerRamificationGroup_add T K hσ ht

/-- Normality of the actual lower groups inside inertia. -/
theorem inertiaLowerGroup_isNormal (i : ℕ) : (inertiaLowerGroup T K i).Normal :=
  (inferInstance : (lowerRamificationGroup T K i).Normal).subgroupOf _

local instance (i : ℕ) : (inertiaLowerGroup T K i).Normal := inertiaLowerGroup_isNormal T K i

/-- The residue of the factor by which an inertia automorphism moves the
specified uniformizer. Its values are in the residue field's units. -/
def tameInertiaCharacter (ϖ : T.Integers) (hϖ : Irreducible ϖ)
    (hmax : maximalIdeal T.Integers = Ideal.span {ϖ}) : inertia T K →* T.ResidueFieldˣ := by
  let := integerAction T K
  have h : inertia T K ≤ lowerGroup T.Integers (L.Carrier ≃ₐ[K] L.Carrier) 0 :=
    (lowerRamificationGroup_zero T K).symm.le
  exact (uniformizerCharacter hmax hϖ.ne_zero).toHomUnits.comp (Subgroup.inclusion h)

/-- The kernel of the residue character is contained in the first lower group. -/
theorem tameInertiaCharacter_ker_le (ϖ : T.Integers) (hϖ : Irreducible ϖ)
    (hmax : maximalIdeal T.Integers = Ideal.span {ϖ}) :
    (tameInertiaCharacter T K ϖ hϖ hmax).ker ≤ inertiaLowerGroup T K 1 := by
  let := integerAction T K
  let := T.residueCharP
  have := T.finite_residueField
  have hpm : (p : T.Integers) ∈ maximalIdeal T.Integers := by
    rw [← residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero T.ResidueField p
  have hfrob : ∀ x : T.Integers, ∃ y : T.Integers, x - y ^ p ∈ maximalIdeal T.Integers := by
    intro x
    obtain ⟨c, hc⟩ := surjective_frobenius T.ResidueField p (residue T.Integers x)
    obtain ⟨y, rfl⟩ := residue_surjective c
    refine ⟨y, ?_⟩
    rw [← residue_eq_zero_iff, map_sub, map_pow, sub_eq_zero, ← hc, frobenius_def]
  intro z hz
  have h0 : (z : L.Carrier ≃ₐ[K] L.Carrier) ∈
      lowerGroup T.Integers (L.Carrier ≃ₐ[K] L.Carrier) 0 :=
    (lowerRamificationGroup_zero T K).symm.le z.property
  let z' : lowerGroup T.Integers (L.Carrier ≃ₐ[K] L.Carrier) 0 := ⟨z, h0⟩
  have hchar : uniformizerCharacter hmax hϖ.ne_zero z' = 1 :=
    congrArg Units.val (MonoidHom.mem_ker.mp hz)
  change (z : L.Carrier ≃ₐ[K] L.Carrier) ∈ lowerRamificationGroup T K 1
  exact mem_lowerGroup_one_of_frobenius hmax Fact.out hpm hfrob h0
    (smul_uniformizer_sub_mem_of_eq_one hmax hϖ.ne_zero hchar)

/-- The quotient of finite inertia by its first lower group is cyclic, and
its index is prime to the residue characteristic. -/
theorem inertia_quotient_lowerOne_cyclic_coprime :
    IsCyclic ((inertia T K) ⧸ (inertiaLowerGroup T K 1)) ∧
      Nat.Coprime (inertiaLowerGroup T K 1).index p := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.residueCharP
  have := T.finite_residueField
  have : IsDiscreteValuationRing T.Integers := inferInstance
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.Integers
  let θ := tameInertiaCharacter T K ϖ hϖ hϖ.maximalIdeal_eq
  let N := inertiaLowerGroup T K 1
  have hN : θ.ker ≤ N := tameInertiaCharacter_ker_le T K ϖ hϖ hϖ.maximalIdeal_eq
  let e := QuotientGroup.quotientKerEquivRange θ
  let : Finite T.ResidueFieldˣ := Finite.of_injective Units.val Units.val_injective
  let : IsCyclic (inertia T K ⧸ θ.ker) := isCyclic_of_surjective e.symm e.symm.surjective
  let f := QuotientGroup.map θ.ker N (MonoidHom.id (inertia T K)) (by simpa using hN)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective N q
    exact ⟨QuotientGroup.mk' θ.ker z, rfl⟩
  refine ⟨isCyclic_of_surjective f hf, ?_⟩
  have hdiv : N.index ∣ Nat.card T.ResidueFieldˣ := by
    change Nat.card (inertia T K ⧸ N) ∣ _
    refine (Subgroup.card_dvd_of_surjective f hf).trans ?_
    rw [Nat.card_congr e.toEquiv]
    exact Subgroup.card_subgroup_dvd_card θ.range
  have hchar : addOrderOf (1 : T.ResidueField) = p :=
    CharP.eq T.ResidueField (CharP.addOrderOf_one _) inferInstance
  have hq : p ∣ Nat.card T.ResidueField := by
    have h := addOrderOf_dvd_natCard (1 : T.ResidueField)
    rwa [hchar] at h
  have hup : ¬ p ∣ Nat.card T.ResidueFieldˣ := by
    rw [Nat.card_units]
    intro h
    have hpos : 0 < Nat.card T.ResidueField := Nat.card_pos
    have hsub : Nat.card T.ResidueField - (Nat.card T.ResidueField - 1) = 1 := by omega
    have h' := Nat.dvd_sub hq h
    rw [hsub, Nat.dvd_one] at h'
    exact (Fact.out : p.Prime).ne_one h'
  exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr fun hp => hup (hp.trans hdiv)).symm

end Langlands.Ramification.HerbrandBridge
