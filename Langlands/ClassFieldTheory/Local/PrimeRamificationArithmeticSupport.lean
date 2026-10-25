import Langlands.Galois.Local.TotallyRamifiedSolvabilityProof
import Mathlib.GroupTheory.OrderOfElement

/-! Canonical total inertia for the supplied relative algebra. -/

noncomputable section

namespace Langlands.Ramification

open IsLocalRing

universe u v

variable {R : Type u} {G : Type v} [CommRing R] [IsLocalRing R] [Group G]
  [MulSemiringAction G R]

/-- Modulo the next ideal power, iterating an element of a positive lower group
adds its first displacement. -/
theorem pow_smul_sub_nsmul_mem {i : ℕ} (hi : 1 ≤ i) {g : G}
    (hg : g ∈ lowerGroup R G i) (n : ℕ) (x : R) :
    (g ^ n • x - x) - n • (g • x - x) ∈ maximalIdeal R ^ (i + 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hd := smul_sub_mem_pow_add ((lowerGroup R G i).pow_mem hg n)
      (k := i + 1) (by omega) (hg x)
    have hd' : g ^ n • (g • x - x) - (g • x - x) ∈ maximalIdeal R ^ (i + 2) :=
      Ideal.pow_le_pow_right (by omega) hd
    have e : (g ^ (n + 1) • x - x) - (n + 1) • (g • x - x) =
        (g ^ n • (g • x - x) - (g • x - x)) +
          ((g ^ n • x - x) - n • (g • x - x)) := by
      simp only [pow_succ, mul_smul, smul_sub, succ_nsmul]
      abel
    rw [e]
    exact add_mem hd' ih

/-- Raising an element of a positive lower group to an exponent whose cast lies
in the maximal ideal moves it to the next lower group. -/
theorem pow_mem_lowerGroup_succ_of_natCast_mem {i n : ℕ} (hi : 1 ≤ i)
    (hn : (n : R) ∈ maximalIdeal R) {g : G} (hg : g ∈ lowerGroup R G i) :
    g ^ n ∈ lowerGroup R G (i + 1) := by
  intro x
  change g ^ n • x - x ∈ maximalIdeal R ^ (i + 2)
  have hmul : n • (g • x - x) ∈ maximalIdeal R ^ (i + 2) := by
    rw [nsmul_eq_mul]
    have h := Ideal.mul_mem_mul hn (hg x)
    rwa [show maximalIdeal R * maximalIdeal R ^ (i + 1) =
      maximalIdeal R ^ (i + 2) from (pow_succ' _ (i + 1)).symm] at h
  have h := add_mem (pow_smul_sub_nsmul_mem hi hg n x) hmul
  simpa only [sub_add_cancel] using h

/-- A terminating positive lower filtration cannot start with the whole nontrivial
group if the residue exponent is coprime to its cardinality. -/
theorem lowerGroup_one_ne_top_of_coprime [Nontrivial G] {n : ℕ}
    (hn : (n : R) ∈ maximalIdeal R) (hcop : (Nat.card G).Coprime n)
    (hbot : ∃ b : ℕ, lowerGroup R G b = ⊥) : lowerGroup R G 1 ≠ ⊤ := by
  intro htop
  have hall : ∀ k : ℕ, lowerGroup R G (k + 1) = ⊤ := by
    intro k
    induction k with
    | zero => exact htop
    | succ k ih =>
      refine eq_top_iff.mpr fun g _ => ?_
      obtain ⟨h, rfl⟩ := (powCoprime hcop).surjective g
      change h ^ n ∈ lowerGroup R G (k + 1 + 1)
      apply pow_mem_lowerGroup_succ_of_natCast_mem (by omega) hn
      rw [ih]
      trivial
  obtain ⟨b, hb⟩ := hbot
  have hle := lowerGroup_antitone R G (Nat.le_succ b)
  rw [hall b, hb] at hle
  exact top_ne_bot (le_bot_iff.mp hle)

/-- A group of exponent equal to the residue characteristic, with fixed residue
representatives, acts trivially to first order. -/
theorem lowerGroup_one_eq_top_of_exponent_char [IsDomain R]
    {p : ℕ} [Fact p.Prime] [CharP (ResidueField R) p]
    {ϖ : R} (hϖ : maximalIdeal R = Ideal.span {ϖ}) (hϖ0 : ϖ ≠ 0)
    (hrep : ∀ x : R, ∃ a : R, (∀ g : G, g • a = a) ∧ x - a ∈ maximalIdeal R)
    (hexp : ∀ g : G, g ^ p = 1) : lowerGroup R G 1 = ⊤ := by
  have hzero := lowerGroup_zero_eq_top_of_fixed hrep
  refine eq_top_iff.mpr fun g _ => ?_
  have hg : g ∈ lowerGroup R G 0 := by rw [hzero]; trivial
  let g' : lowerGroup R G 0 := ⟨g, hg⟩
  have hgpow : g' ^ p = 1 := Subtype.ext (hexp g)
  have hθpow : (uniformizerCharacter hϖ hϖ0 g') ^ p = 1 := by
    rw [← map_pow, hgpow, map_one]
  have hθ : uniformizerCharacter hϖ hϖ0 g' = 1 := by
    apply sub_eq_zero.mp
    apply (pow_eq_zero_iff (Fact.out : p.Prime).ne_zero).mp
    rw [sub_pow_char, hθpow, one_pow, sub_self]
  exact mem_lowerGroup_one_of_fixed hϖ hrep hg
    (smul_uniformizer_sub_mem_of_eq_one hϖ hϖ0 hθ)

end Langlands.Ramification

namespace Langlands.LocalClassField

open Langlands.Weil.Local Langlands.Ramification IsLocalRing

universe u v

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (L : PadicField.{v} p)
  [Algebra F.Carrier L.Carrier] [IsScalarTower (Padic p) F.Carrier L.Carrier]

/-- The degree of the compatible embedding is the degree of the supplied algebra. -/
theorem extensionDegree_suppliedAlgebra :
    extensionDegree F L (IsScalarTower.toAlgHom (Padic p) F.Carrier L.Carrier) =
      Module.finrank F.Carrier L.Carrier := by
  have h : extensionAlgebra F L (IsScalarTower.toAlgHom (Padic p) F.Carrier L.Carrier) =
      (inferInstance : Algebra F.Carrier L.Carrier) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  unfold extensionDegree
  rw [h]

/-- Canonical total ramification forces the relative residue degree to be one. -/
theorem extensionResidueDegree_supplied_eq_one
    (h : L.canonicalTopologicalData.ramificationIndex =
      Module.finrank F.Carrier L.Carrier * F.canonicalTopologicalData.ramificationIndex) :
    extensionResidueDegree F L (IsScalarTower.toAlgHom (Padic p) F.Carrier L.Carrier) = 1 := by
  have key := PadicField.ramificationIndex_mul_extensionResidueDegree F L
    (IsScalarTower.toAlgHom (Padic p) F.Carrier L.Carrier)
  rw [extensionDegree_suppliedAlgebra, ← h] at key
  exact Nat.eq_of_mul_eq_mul_left L.canonicalTopologicalData.ramificationIndex_pos
    (key.trans (mul_one _).symm)

/-- Relative residue degree one supplies residue representatives fixed by the actual
base-field automorphism group. -/
theorem fixedResidueRepresentatives_suppliedAlgebra
    (hres : extensionResidueDegree F L
      (IsScalarTower.toAlgHom (Padic p) F.Carrier L.Carrier) = 1) :
    letI := Padic.integerAction L.canonicalTopologicalData F.Carrier
    ∀ x : L.canonicalTopologicalData.Integers, ∃ a : L.canonicalTopologicalData.Integers,
      (∀ σ : Gal(L.Carrier/F.Carrier), σ • a = a) ∧
        x - a ∈ maximalIdeal L.canonicalTopologicalData.Integers := by
  let := Padic.integerAction L.canonicalTopologicalData F.Carrier
  let := extensionResidueAlgebra F L
    (IsScalarTower.toAlgHom (Padic p) F.Carrier L.Carrier)
  intro x
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
    (1 : L.canonicalTopologicalData.ResidueField) one_ne_zero).mp hres
      (L.canonicalTopologicalData.residue x)
  obtain ⟨y, rfl⟩ := residue_surjective c
  refine ⟨extensionIntegerMap F L
    (IsScalarTower.toAlgHom (Padic p) F.Carrier L.Carrier) y, fun σ => ?_, ?_⟩
  · apply Subtype.ext
    exact σ.commutes (y : F.Carrier)
  · rw [← residue_eq_zero_iff, map_sub, sub_eq_zero, ← hc, Algebra.smul_def, mul_one]
    rfl

/-- Canonical total ramification makes the actual inertia group the whole group. -/
theorem inertia_eq_top_of_canonical_totalRamification
    (h : L.canonicalTopologicalData.ramificationIndex =
      Module.finrank F.Carrier L.Carrier * F.canonicalTopologicalData.ramificationIndex) :
    Padic.inertia L.canonicalTopologicalData F.Carrier = ⊤ := by
  rw [← Padic.lowerRamificationGroup_zero]
  let := Padic.integerAction L.canonicalTopologicalData F.Carrier
  exact lowerGroup_zero_eq_top_of_fixed
    (fixedResidueRepresentatives_suppliedAlgebra F L
      (extensionResidueDegree_supplied_eq_one F L h))

/-- The first actual lower group is the whole group exactly in the wild case,
for a prime-degree canonically totally ramified extension. -/
theorem lowerRamificationGroup_one_eq_top_iff_prime_degree
    [FiniteDimensional F.Carrier L.Carrier] [IsGalois F.Carrier L.Carrier]
    (hell : Nat.Prime (Module.finrank F.Carrier L.Carrier))
    (htot : L.canonicalTopologicalData.ramificationIndex =
      Module.finrank F.Carrier L.Carrier * F.canonicalTopologicalData.ramificationIndex) :
    Padic.lowerRamificationGroup L.canonicalTopologicalData F.Carrier 1 = ⊤ ↔
      Module.finrank F.Carrier L.Carrier = p := by
  let T := L.canonicalTopologicalData
  let := Padic.integerAction T F.Carrier
  have hcard := IsGalois.card_aut_eq_finrank F.Carrier L.Carrier
  have : Nontrivial Gal(L.Carrier/F.Carrier) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; exact hell.one_lt)
  have : IsDiscreteValuationRing T.Integers := by
    let := T.topology
    let := T.valuativeRel
    let := T.localField
    infer_instance
  let := T.residueCharP
  have hpm : (p : T.Integers) ∈ maximalIdeal T.Integers := by
    rw [← residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero T.ResidueField p
  constructor
  · intro htop
    by_contra hne
    have hcop : (Nat.card Gal(L.Carrier/F.Carrier)).Coprime p := by
      rw [hcard]
      exact (Nat.coprime_primes hell (Fact.out : p.Prime)).mpr hne
    obtain ⟨b, hb⟩ := Padic.exists_lowerRamificationGroup_eq_bot T F.Carrier
    exact lowerGroup_one_ne_top_of_coprime hpm hcop ⟨b, hb b le_rfl⟩ htop
  · intro heq
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.Integers
    apply lowerGroup_one_eq_top_of_exponent_char hϖ.maximalIdeal_eq hϖ.ne_zero
      (fixedResidueRepresentatives_suppliedAlgebra F L
        (extensionResidueDegree_supplied_eq_one F L htot))
    intro g
    simpa only [hcard, heq] using (pow_card_eq_one' (x := g))

end Langlands.LocalClassField
