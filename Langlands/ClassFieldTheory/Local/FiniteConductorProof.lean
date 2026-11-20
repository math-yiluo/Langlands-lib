import Langlands.LocalFactor.Ramification.Herbrand.QuotientProof
import Langlands.ClassFieldTheory.Local.FiniteConductorStatement
import Langlands.ClassFieldTheory.Local.UpperReciprocityProof
import Langlands.ClassFieldTheory.Local.UnitFiltrationConductor
import Langlands.ClassFieldTheory.Local.UnitFiltrationStructuralProof
import Langlands.LocalFactor.Ramification.RankOneArtinSum

/-!
# Finite-character conductor transport under local reciprocity: proof

This module proves `Langlands.LocalClassField.FiniteCharacterConductorTheorems`.
Every clause is derived from the published upper-numbering bundle
`finiteUpperReciprocityTheorems`, the unit-filtration comparison and conductor
criterion, and the rank-one Artin expression of an inertia character through its
upper levels. Auxiliary facts about an actual finite extension are proved here:
Herbrand's function at `1` lies in `(0, 1]`, so `G^(φ(1)) = G_1` and `⌈φ(1)⌉ = 1`;
the Artin expression of a Galois representation and the inertia Artin expression
are finite sums over the lower groups; and the Artin expression of a Galois
representation equals the inertia Artin expression of its restriction to inertia.
-/

noncomputable section

namespace Langlands.Ramification.Padic

open Module

universe uK uL uk uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
  (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
  [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]

/-- Herbrand's function at `1` is `|G_1| / |G_0|`, which lies in `(0, 1]`. -/
theorem herbrandPhi_one_mem_Ioc : herbrandPhi T K 1 ∈ Set.Ioc (0 : ℝ) 1 := by
  refine ⟨herbrandPhi_pos T K one_pos, ?_⟩
  have : Finite (F.Carrier ≃ₐ[K] F.Carrier) := by
    have : FiniteDimensional K F.Carrier :=
      Module.Finite.of_restrictScalars_finite (Padic p) K F.Carrier
    infer_instance
  have hle : lowerGroupOrder T K 1 ≤ lowerGroupOrder T K 0 :=
    Subgroup.card_le_of_le (lowerRamificationGroup_antitone T K (Nat.zero_le 1))
  have h := herbrandPhi_natCast T K 1
  rw [Nat.cast_one, Finset.sum_range_one, zero_add] at h
  rw [h, div_le_one (by exact_mod_cast lowerGroupOrder_pos T K 0)]
  exact_mod_cast hle

/-- The integer ceiling of Herbrand's function at `1` is `1`. -/
theorem natCeil_herbrandPhi_one : ⌈herbrandPhi T K 1⌉₊ = 1 := by
  obtain ⟨h0, h1⟩ := herbrandPhi_one_mem_Ioc T K
  rw [Nat.ceil_eq_iff one_ne_zero, Nat.sub_self, Nat.cast_zero, Nat.cast_one]
  exact ⟨h0, h1⟩

/-- The upper group at `φ(1)` is the first lower ramification group. -/
theorem upperRamificationGroup_herbrandPhi_one :
    upperRamificationGroup T K (herbrandPhi T K 1) = lowerRamificationGroup T K 1 := by
  rw [upperRamificationGroup_phi]
  have h := lowerRamificationGroupReal_nat T K 1
  rwa [Nat.cast_one] at h

/-- Every nonnegatively indexed upper group lies in inertia. -/
theorem upperRamificationGroup_le_inertia {v : ℝ} (hv : 0 ≤ v) :
    upperRamificationGroup T K v ≤ inertia T K := by
  rw [← upperRamificationGroup_zero T K]
  exact upperRamificationGroup_antitone T K hv

/-- Every nonnegatively indexed lower group lies in inertia. -/
theorem lowerRamificationGroup_le_inertia (i : ℕ) :
    lowerRamificationGroup T K i ≤ inertia T K := by
  rw [← lowerRamificationGroup_zero T K]
  exact lowerRamificationGroup_antitone T K (Nat.zero_le i)

/-- Inertia acts faithfully on the supplied integer ring. -/
theorem inertiaIntegerAction_faithfulSMul :
    letI := inertiaIntegerAction T K
    FaithfulSMul (inertia T K) T.Integers := by
  let := inertiaIntegerAction T K
  let := integerAction T K
  have := Langlands.Ramification.HerbrandBridge.integerAction_faithful T K
  refine ⟨fun {σ τ} h => Subtype.ext ?_⟩
  exact FaithfulSMul.eq_of_smul_eq_smul (α := T.Integers) h

/-- The supplied integer ring is Noetherian. -/
theorem integers_isNoetherianRing : IsNoetherianRing T.Integers := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

/-- The automorphism group of the finite extension is finite. -/
theorem automorphismGroup_finite_of_padic : Finite (F.Carrier ≃ₐ[K] F.Carrier) := by
  have : FiniteDimensional K F.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) K F.Carrier
  infer_instance

variable {k : Type uk} [Field k] {V : Type uV} [AddCommGroup V] [Module k V]

omit [Fact p.Prime] [Field K] [Algebra (Padic p) K] [Algebra K F.Carrier]
  [IsScalarTower (Padic p) K F.Carrier] in
/-- Restricting to inertia does not change the vectors fixed by a subgroup of
inertia. -/
theorem fixedVectors_comp_subtype_subgroupOf {G : Type*} [Group G] (I : Subgroup G)
    (ρ : Representation k G V) {H : Subgroup G} (hH : H ≤ I) :
    fixedVectors (ρ.comp I.subtype) (H.subgroupOf I) = fixedVectors ρ H := by
  ext v
  change (∀ g : H.subgroupOf I, ρ ((g : I) : G) v = v) ↔ ∀ g : H, ρ g v = v
  constructor
  · intro h g
    exact h ⟨⟨g, hH g.2⟩, Subgroup.mem_subgroupOf.mpr g.2⟩
  · intro h g
    exact h ⟨(g : I), Subgroup.mem_subgroupOf.mp g.2⟩

variable [FiniteDimensional k V]

/-- The Artin expression of a representation of the actual finite Galois group,
as the finite sum over the lower groups below a vanishing bound. -/
theorem artinConductor_eq_sum_range_lower
    (ρ : Representation k (F.Carrier ≃ₐ[K] F.Carrier) V) (b : ℕ)
    (hb : ∀ i ≥ b, lowerRamificationGroup T K i = ⊥) :
    artinConductor T K ρ = ∑ i ∈ Finset.range b,
      (Nat.card (lowerRamificationGroup T K i) : ℚ) /
          Nat.card (lowerRamificationGroup T K 0) *
        ((finrank k V - finrank k (fixedVectors ρ (lowerRamificationGroup T K i)) : ℕ) :
          ℚ) := by
  let := integerAction T K
  have := Langlands.Ramification.HerbrandBridge.integerAction_faithful T K
  have := integers_isNoetherianRing T
  have := automorphismGroup_finite_of_padic (F := F) K
  exact Ramification.artinConductor_eq_sum_range T.Integers _ ρ b hb

/-- The inertia Artin expression, as the finite sum over the lower groups of
inertia below a vanishing bound of the full lower filtration. -/
theorem inertiaArtinConductor_eq_sum_range_lower
    (ρ : Representation k (inertia T K) V) (b : ℕ)
    (hb : ∀ i ≥ b, lowerRamificationGroup T K i = ⊥) :
    inertiaArtinConductor T K ρ = ∑ i ∈ Finset.range b,
      (Nat.card (inertiaLowerGroup T K i) : ℚ) / Nat.card (inertiaLowerGroup T K 0) *
        ((finrank k V - finrank k (fixedVectors ρ (inertiaLowerGroup T K i)) : ℕ) : ℚ) := by
  let := inertiaIntegerAction T K
  have := inertiaIntegerAction_faithfulSMul T K
  have := integers_isNoetherianRing T
  have := automorphismGroup_finite_of_padic (F := F) K
  have hb' : ∀ i ≥ b, lowerGroup T.Integers (inertia T K) i = ⊥ := by
    intro i hi
    change inertiaLowerGroup T K i = ⊥
    rw [inertiaLowerGroup, hb i hi, Subgroup.bot_subgroupOf]
  exact Ramification.artinConductor_eq_sum_range T.Integers _ ρ b hb'

/-- The Artin expression of a representation of the actual finite Galois group
equals the inertia Artin expression of its restriction to inertia: the lower groups
of inertia are the lower groups of the full group, with the same orders and the
same fixed vectors. -/
theorem artinConductor_eq_inertiaArtinConductor_comp
    (ρ : Representation k (F.Carrier ≃ₐ[K] F.Carrier) V) :
    artinConductor T K ρ = inertiaArtinConductor T K (ρ.comp (inertia T K).subtype) := by
  obtain ⟨b, hb⟩ := exists_lowerRamificationGroup_eq_bot T K
  rw [artinConductor_eq_sum_range_lower T K ρ b hb,
    inertiaArtinConductor_eq_sum_range_lower T K _ b hb]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcard : ∀ j : ℕ, Nat.card (inertiaLowerGroup T K j) =
      Nat.card (lowerRamificationGroup T K j) := fun j =>
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (lowerRamificationGroup_le_inertia T K j)).toEquiv
  have hfix : fixedVectors (ρ.comp (inertia T K).subtype) (inertiaLowerGroup T K i) =
      fixedVectors ρ (lowerRamificationGroup T K i) :=
    fixedVectors_comp_subtype_subgroupOf (inertia T K) ρ
      (lowerRamificationGroup_le_inertia T K i)
  rw [hcard, hcard, hfix]

/-- **Rank-one Artin expression of a Galois character through its upper levels.**
If the character `χ` of the actual finite Galois group is trivial on the upper
group `G^s` exactly when `a ≤ ⌈s⌉` (for every real `s ≥ 0`), then the Artin
expression of the corresponding one-dimensional representation is `a`. -/
theorem artinConductor_rankOne_eq_of_upper_levels
    (χ : (F.Carrier ≃ₐ[K] F.Carrier) →* ℂˣ) (a : ℕ)
    (h : ∀ s : ℝ, 0 ≤ s →
      (a ≤ ⌈s⌉₊ ↔ ∀ σ ∈ upperRamificationGroup T K s, χ σ = 1)) :
    artinConductor T K (LocalClassField.rankOneCharacterRepresentation χ) = a := by
  rw [artinConductor_eq_inertiaArtinConductor_comp]
  have hcomp : (LocalClassField.rankOneCharacterRepresentation χ).comp (inertia T K).subtype =
      LocalClassField.rankOneCharacterRepresentation (χ.comp (inertia T K).subtype) := by
    ext σ
    simp
  rw [hcomp]
  refine inertiaArtinConductor_rankOne_eq_of_upper_levels T K _ a fun s hs => ?_
  rw [h s hs]
  constructor
  · intro hχ σ hσ
    exact hχ σ hσ
  · intro hχ σ hσ
    exact hχ ⟨σ, upperRamificationGroup_le_inertia T K hs hσ⟩ hσ

end Langlands.Ramification.Padic

namespace Langlands.LocalClassField

open Ramification.Padic

universe u

/-- Reciprocity carries the units onto inertia and the first principal units onto
the first lower ramification group. -/
theorem finiteReciprocityInertiaImages : FiniteReciprocityInertiaImages.{u} := by
  obtain ⟨hHigher, hReal, -, -, -⟩ := finiteUpperReciprocityTheorems.{u}
  intro p _ F T r hr L S
  let := T.topology
  let : Algebra F.Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (Algebra F.Carrier L.field)
  have : IsScalarTower (Padic p) F.Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (IsScalarTower (Padic p) F.Carrier L.field)
  have h0 := hHigher p F T r hr L S 0
  rw [Nat.cast_zero, upperRamificationGroup_zero, T.unitFiltration_zero] at h0
  have h1 := hReal p F T r hr L S (herbrandPhi S F.Carrier 1)
    (herbrandPhi_one_mem_Ioc S F.Carrier).1.le
  rw [natCeil_herbrandPhi_one] at h1
  exact ⟨h0, h1.trans (upperRamificationGroup_herbrandPhi_one S F.Carrier)⟩

/-- The multiplicative conductor of the transported character is the Artin
expression of the finite character. -/
theorem finiteReciprocityConductorTransport : FiniteReciprocityConductorTransport.{u} := by
  obtain ⟨-, -, -, hLevels, -⟩ := finiteUpperReciprocityTheorems.{u}
  intro p _ F T r hr L S χ
  let := T.topology
  let : Algebra F.Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (Algebra F.Carrier L.field)
  have : IsScalarTower (Padic p) F.Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (IsScalarTower (Padic p) F.Carrier L.field)
  have key := artinConductor_rankOne_eq_of_upper_levels S F.Carrier
  exact (key χ.toMonoidHom _ (hLevels p F T r hr L S χ)).symm

/-- The Artin expression is at most `n` exactly when the transported character
kills the `n`th unit level. -/
theorem finiteReciprocityConductorLevels : FiniteReciprocityConductorLevels.{u} := by
  intro p _ F T r hr L S χ n
  let := T.topology
  have h3 := finiteReciprocityConductorTransport p F T r hr L S χ
  exact (iff_of_eq (congrArg (· ≤ (n : ℚ)) h3.symm)).trans
    (Nat.cast_le.trans (T.multiplicativeConductor_le_iff_unitFiltration_le_ker _ n))

/-- Conductor zero is triviality on inertia; conductor at most one is triviality
on the first lower ramification group. -/
theorem finiteReciprocityUnramifiedTameCharacters :
    FiniteReciprocityUnramifiedTameCharacters.{u} := by
  obtain ⟨-, -, -, hLevels, -⟩ := finiteUpperReciprocityTheorems.{u}
  intro p _ F T r hr L S χ
  let := T.topology
  let : Algebra F.Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (Algebra F.Carrier L.field)
  have : IsScalarTower (Padic p) F.Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (IsScalarTower (Padic p) F.Carrier L.field)
  have h0 := hLevels p F T r hr L S χ 0 le_rfl
  rw [Nat.ceil_zero, upperRamificationGroup_zero] at h0
  have h1 := hLevels p F T r hr L S χ (herbrandPhi S F.Carrier 1)
    (herbrandPhi_one_mem_Ioc S F.Carrier).1.le
  rw [natCeil_herbrandPhi_one] at h1
  have e := upperRamificationGroup_herbrandPhi_one S F.Carrier
  exact ⟨Nat.le_zero.symm.trans h0,
    h1.trans ⟨fun h σ hσ => h σ ((SetLike.ext_iff.mp e σ).mpr hσ),
      fun h σ hσ => h σ ((SetLike.ext_iff.mp e σ).mp hσ)⟩⟩

/-- **Finite-character conductor theorems.** Under normalized geometric local
reciprocity, units go to inertia, first principal units to the first lower group,
and the Artin expression of a finite character is the multiplicative conductor of
the transported character, with the derived level and tame criteria. -/
theorem finiteCharacterConductorTheorems : FiniteCharacterConductorTheorems.{u} :=
  ⟨unitFiltrationComparison, finiteReciprocityInertiaImages,
    finiteReciprocityConductorTransport, finiteReciprocityConductorLevels,
    finiteReciprocityUnramifiedTameCharacters⟩

end Langlands.LocalClassField
