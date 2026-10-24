import Langlands.LocalFactor.Ramification.InertiaSolvabilityStatement
import Langlands.Galois.Local.TotallyRamifiedSolvabilityProof
import Langlands.LocalField.Normalization.Proof

/-!
# Proof of solvability of actual finite p-adic inertia groups

For a group acting on a discrete valuation ring whose residue field has surjective
Frobenius and residue characteristic `p`, an element of `G_0` that moves a uniformizer by
an element of `m ^ 2` lies in `G_1`: it moves `p`-th powers and elements of `m` by elements
of `m ^ 2`, and these generate every residue class. Commutators of `G_0` act trivially on
the uniformizer modulo `m ^ 2`, so `G_0 / G_1` is abelian. The derived series of `G_0`
therefore lies in the lower ramification filtration, which terminates. The residue field
of every finite extension of `Padic p` is finite of characteristic `p`.
-/

noncomputable section

namespace Langlands.Ramification

open IsLocalRing
open scoped commutatorElement

universe u v

section Frobenius

variable {R : Type u} {G : Type v} [CommRing R] [IsLocalRing R] [Group G]
  [MulSemiringAction G R] {ϖ : R} (hϖ : maximalIdeal R = Ideal.span {ϖ})

include hϖ in
/-- An element of `G_0` moving `ϖ` by an element of `m ^ 2` moves every element of `m` by an
element of `m ^ 2`. -/
theorem smul_sub_mem_sq_of_mem_maximalIdeal {g : G} (hg : g ∈ lowerGroup R G 0)
    (hgϖ : g • ϖ - ϖ ∈ maximalIdeal R ^ 2) {b : R} (hb : b ∈ maximalIdeal R) :
    g • b - b ∈ maximalIdeal R ^ 2 := by
  rw [hϖ, Ideal.mem_span_singleton'] at hb
  obtain ⟨c, rfl⟩ := hb
  have e : g • (c * ϖ) - c * ϖ = (g • c) * (g • ϖ - ϖ) + (g • c - c) * ϖ := by
    rw [smul_mul']
    ring
  have hg' : g ∈ congruenceGroup R G (0 + 1) := hg
  have hc : g • c - c ∈ maximalIdeal R := by simpa using hg' c
  have hϖm : ϖ ∈ maximalIdeal R := by
    rw [hϖ]
    exact Ideal.mem_span_singleton_self ϖ
  rw [e]
  refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hgϖ) ?_
  rw [pow_two]
  exact Ideal.mul_mem_mul hc hϖm

/-- If `p` is a prime lying in `m`, every element of `G_0` moves each `p`-th power by an
element of `m ^ 2`. -/
theorem smul_pow_sub_mem_sq {p : ℕ} (hp : p.Prime) (hpm : (p : R) ∈ maximalIdeal R)
    {g : G} (hg : g ∈ lowerGroup R G 0) (y : R) :
    g • (y ^ p) - y ^ p ∈ maximalIdeal R ^ 2 := by
  have hg' : g ∈ congruenceGroup R G (0 + 1) := hg
  have hd : g • y - y ∈ maximalIdeal R := by simpa using hg' y
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp y (g • y - y)
  rw [show y + (g • y - y) = g • y by abel] at hr
  have e : g • (y ^ p) - y ^ p = (g • y - y) ^ p + ((p : R) * (g • y - y)) * (y * r) := by
    rw [smul_pow', hr]
    ring
  rw [e]
  refine Ideal.add_mem _ ?_ ?_
  · exact Ideal.pow_le_pow_right hp.two_le (Ideal.pow_mem_pow hd p)
  · rw [pow_two]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul hpm hd)

include hϖ in
/-- If Frobenius is surjective on residue classes, an element of `G_0` moving `ϖ` by an
element of `m ^ 2` lies in `G_1`. -/
theorem mem_lowerGroup_one_of_frobenius {p : ℕ} (hp : p.Prime)
    (hpm : (p : R) ∈ maximalIdeal R) (hfrob : ∀ x : R, ∃ y : R, x - y ^ p ∈ maximalIdeal R)
    {g : G} (hg : g ∈ lowerGroup R G 0) (hgϖ : g • ϖ - ϖ ∈ maximalIdeal R ^ 2) :
    g ∈ lowerGroup R G 1 := by
  intro x
  obtain ⟨y, hy⟩ := hfrob x
  have e : g • x - x = (g • (y ^ p) - y ^ p) + (g • (x - y ^ p) - (x - y ^ p)) := by
    rw [smul_sub]
    abel
  rw [e, show 1 + 1 = 2 from rfl]
  exact Ideal.add_mem _ (smul_pow_sub_mem_sq hp hpm hg y)
    (smul_sub_mem_sq_of_mem_maximalIdeal hϖ hg hgϖ hy)

variable [IsDomain R] (hϖ0 : ϖ ≠ 0) {p : ℕ} (hp : p.Prime) (hpm : (p : R) ∈ maximalIdeal R)
  (hfrob : ∀ x : R, ∃ y : R, x - y ^ p ∈ maximalIdeal R)

include hϖ hϖ0 hp hpm hfrob in
/-- If Frobenius is surjective on residue classes of characteristic `p`, then `G_0 / G_1`
is abelian. -/
theorem commutator_lowerGroup_zero_le_of_frobenius :
    ⁅lowerGroup R G 0, lowerGroup R G 0⁆ ≤ lowerGroup R G 1 := by
  refine Subgroup.commutator_le.mpr fun g hg h hh => ?_
  let g' : lowerGroup R G 0 := ⟨g, hg⟩
  let h' : lowerGroup R G 0 := ⟨h, hh⟩
  have hθ : uniformizerCharacter hϖ hϖ0 ⁅g', h'⁆ = 1 := by
    have hu : (uniformizerCharacter hϖ hϖ0).toHomUnits ⁅g', h'⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]
    have hv := congrArg Units.val hu
    rwa [MonoidHom.coe_toHomUnits, Units.val_one] at hv
  exact mem_lowerGroup_one_of_frobenius hϖ hp hpm hfrob (⁅g', h'⁆).2
    (smul_uniformizer_sub_mem_of_eq_one hϖ hϖ0 hθ)

include hϖ hϖ0 hp hpm hfrob in
/-- The derived series of `G_0`, mapped into `G`, lies in the lower ramification
filtration. -/
theorem map_derivedSeries_lowerGroup_zero_le (n : ℕ) :
    (derivedSeries (lowerGroup R G 0) n).map (lowerGroup R G 0).subtype ≤
      lowerGroup R G n := by
  induction n with
  | zero => rw [derivedSeries_zero, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  | succ n ih =>
    rw [derivedSeries_succ, Subgroup.map_commutator]
    refine (Subgroup.commutator_mono ih ih).trans ?_
    rcases n with _ | n
    · exact commutator_lowerGroup_zero_le_of_frobenius hϖ hϖ0 hp hpm hfrob
    · exact commutator_lowerGroup_le_succ (by omega)

include hϖ hϖ0 hp hpm hfrob in
/-- A terminating lower filtration over a residue field with surjective Frobenius makes
`G_0` solvable. -/
theorem isSolvable_lowerGroup_zero_of_frobenius (hbot : ∃ b : ℕ, lowerGroup R G b = ⊥) :
    Group.IsSolvable (lowerGroup R G 0) := by
  obtain ⟨b, hb⟩ := hbot
  have h := map_derivedSeries_lowerGroup_zero_le (G := G) hϖ hϖ0 hp hpm hfrob b
  rw [hb, le_bot_iff] at h
  exact ⟨⟨b, (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp h⟩⟩

end Frobenius

namespace Padic

universe uK uL

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
  (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
  [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]

/-- The actual inertia group of every supplied local-field realization is solvable. -/
theorem isSolvable_inertia : Group.IsSolvable (inertia T K) := by
  let := integerAction T K
  have : IsDiscreteValuationRing T.Integers := by
    let := T.topology
    let := T.valuativeRel
    let := T.localField
    infer_instance
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.Integers
  have hp : p.Prime := Fact.out
  have hpm : (p : T.Integers) ∈ maximalIdeal T.Integers := by
    let := T.residueCharP
    rw [← residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero T.ResidueField p
  have hfrob : ∀ x : T.Integers, ∃ y : T.Integers, x - y ^ p ∈ maximalIdeal T.Integers := by
    let := T.residueCharP
    have := T.finite_residueField
    intro x
    obtain ⟨c, hc⟩ := surjective_frobenius T.ResidueField p (residue T.Integers x)
    obtain ⟨y, rfl⟩ := residue_surjective c
    refine ⟨y, ?_⟩
    rw [← residue_eq_zero_iff, map_sub, map_pow, sub_eq_zero, ← hc, frobenius_def]
  obtain ⟨b, hb⟩ := exists_lowerRamificationGroup_eq_bot T K
  rw [← lowerRamificationGroup_zero]
  exact isSolvable_lowerGroup_zero_of_frobenius hϖ.maximalIdeal_eq hϖ.ne_zero hp hpm hfrob
    ⟨b, hb b le_rfl⟩

end Padic

end Langlands.Ramification

namespace Langlands.Ramification.Padic

universe u v

/-- Solvability of the actual inertia groups of finite Galois extensions of p-adic
fields. -/
theorem finiteInertiaSolvability : FiniteInertiaSolvability.{u, v} := by
  intro p _ K L _ _ _
  exact isSolvable_inertia L.canonicalTopologicalData K.Carrier

end Langlands.Ramification.Padic
