import Langlands.LocalFactor.Ramification.Herbrand.QuotientProof
import Langlands.LocalFactor.Ramification.RankOneArtinSum
import Langlands.LocalFactor.Ramification.HasseArf.CharacterSum

/-!
# Integrality of the Artin and Swan exponents of a character, from upstream's Hasse–Arf

The ported Anthropic FLT theorem
`Langlands.Ramification.exists_finsum_lowerGroup_indicator_eq_natCast` (for a finite
group acting faithfully on a discrete valuation ring with perfect residue field and separable
residue extension, and a character `ψ` into `ℂˣ`, the sum
`Σ_i |G_{i+1}|/|G_0| · [ψ ≠ 1 on G_{i+1}]` is a natural number) is applied to the supplied integer
ring of a finite extension of p-adic fields and its full automorphism group. That sum is the
Library's Swan expression of the one-dimensional representation of the character, so the Swan
and Artin expressions `swanConductor T K` and `artinConductor T K` of every character, and of
every one-dimensional representation, are natural numbers. No reciprocity and no commutativity
of the group is used.
-/

noncomputable section

namespace Langlands.Ramification.Padic

open IsLocalRing Module

universe uK uL uV

/-- The codimension of the vectors fixed by a subgroup in the one-dimensional representation of a
character is `0` if the character is trivial on the subgroup and `1` otherwise. -/
theorem fixedCodimension_rankOne {G : Type*} [Group G] (χ : G →* ℂˣ) (H : Subgroup G)
    [Decidable (∀ h ∈ H, χ h = 1)] :
    fixedCodimension G (LocalClassField.rankOneCharacterRepresentation χ) H =
      if ∀ h ∈ H, χ h = 1 then 0 else 1 := by
  unfold fixedCodimension
  rw [finrank_fixedVectors_rankOne, Module.finrank_self]
  split_ifs <;> rfl

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
  (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
  [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]

open scoped Classical in
/-- **Upstream's theorem for the supplied integer ring.** For a character `χ` of the automorphism
group of `F` over `K`, the sum `Σ_i |G_{i+1}|/|G_0| · [χ ≠ 1 on G_{i+1}]` over the Library's lower
groups `G_i = lowerRamificationGroup T K i` is a natural number. Every hypothesis of the ported
theorem holds for the supplied integer ring and the full automorphism group. -/
theorem exists_finsum_lowerRamificationGroup_indicator_eq_natCast_of_hasseArf
    (χ : (F.Carrier ≃ₐ[K] F.Carrier) →* ℂˣ) :
    ∃ m : ℕ, ∑ᶠ i : ℕ, (lowerGroupOrder T K (i + 1) : ℚ) / (lowerGroupOrder T K 0 : ℚ) *
        (if ∀ σ ∈ lowerRamificationGroup T K (i + 1), χ σ = 1 then 0 else 1) = m := by
  let := integerAction T K
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have _ : IsDiscreteValuationRing T.Integers := inferInstance
  have _ : FiniteDimensional K F.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) K F.Carrier
  have := HerbrandBridge.integerAction_faithful T K
  have _ : Finite T.ResidueField := inferInstance
  have _ : Finite (T.Integers ⧸ maximalIdeal T.Integers) :=
    inferInstanceAs (Finite T.ResidueField)
  have _ : (maximalIdeal T.Integers).LiesOver
      (maximalIdeal (FixedPoints.subring T.Integers (F.Carrier ≃ₐ[K] F.Carrier))) :=
    ⟨maximalIdeal_fixedSubring_eq_comap⟩
  let _ : Field (T.Integers ⧸ maximalIdeal T.Integers) := Ideal.Quotient.field _
  let _ : Field (FixedPoints.subring T.Integers (F.Carrier ≃ₐ[K] F.Carrier) ⧸
      maximalIdeal (FixedPoints.subring T.Integers (F.Carrier ≃ₐ[K] F.Carrier))) :=
    Ideal.Quotient.field _
  have _ : Finite (FixedPoints.subring T.Integers (F.Carrier ≃ₐ[K] F.Carrier) ⧸
      maximalIdeal (FixedPoints.subring T.Integers (F.Carrier ≃ₐ[K] F.Carrier))) :=
    Finite.of_injective (algebraMap _ (T.Integers ⧸ maximalIdeal T.Integers))
      (algebraMap
        (FixedPoints.subring T.Integers (F.Carrier ≃ₐ[K] F.Carrier) ⧸
          maximalIdeal (FixedPoints.subring T.Integers (F.Carrier ≃ₐ[K] F.Carrier)))
        (T.Integers ⧸ maximalIdeal T.Integers)).injective
  exact exists_finsum_lowerGroup_indicator_eq_natCast χ

open scoped Classical in
/-- The Library's Swan expression of the one-dimensional representation of a character is the
sum of upstream's theorem. -/
theorem swanConductor_rankOne_eq_finsum (χ : (F.Carrier ≃ₐ[K] F.Carrier) →* ℂˣ) :
    swanConductor T K (LocalClassField.rankOneCharacterRepresentation χ) =
      ∑ᶠ i : ℕ, (lowerGroupOrder T K (i + 1) : ℚ) / (lowerGroupOrder T K 0 : ℚ) *
        (if ∀ σ ∈ lowerRamificationGroup T K (i + 1), χ σ = 1 then 0 else 1) := by
  let := integerAction T K
  have := HerbrandBridge.integerAction_faithful T K
  have _ : IsNoetherianRing T.Integers := by
    let := T.topology
    let := T.valuativeRel
    let := T.localField
    infer_instance
  have _ : Finite (F.Carrier ≃ₐ[K] F.Carrier) := by
    have _ : FiniteDimensional K F.Carrier :=
      Module.Finite.of_restrictScalars_finite (Padic p) K F.Carrier
    infer_instance
  change Ramification.swanConductor T.Integers (F.Carrier ≃ₐ[K] F.Carrier) _ = _
  rw [Ramification.swanConductor_eq_finsum]
  refine finsum_congr fun i => ?_
  change (lowerGroupOrder T K (i + 1) : ℚ) / (lowerGroupOrder T K 0 : ℚ) *
      (fixedCodimension _ (LocalClassField.rankOneCharacterRepresentation χ)
        (lowerRamificationGroup T K (i + 1)) : ℚ) = _
  rw [fixedCodimension_rankOne]
  split_ifs <;> simp

open scoped Classical in
/-- The Artin expression of a character is its Swan expression plus `1` if the character is
nontrivial on inertia, and plus `0` otherwise. -/
theorem artinConductor_rankOne_eq_add_swanConductor (χ : (F.Carrier ≃ₐ[K] F.Carrier) →* ℂˣ) :
    artinConductor T K (LocalClassField.rankOneCharacterRepresentation χ) =
      ((if ∀ σ ∈ inertia T K, χ σ = 1 then 0 else 1 : ℕ) : ℚ) +
        swanConductor T K (LocalClassField.rankOneCharacterRepresentation χ) := by
  let := integerAction T K
  have := HerbrandBridge.integerAction_faithful T K
  have _ : IsNoetherianRing T.Integers := by
    let := T.topology
    let := T.valuativeRel
    let := T.localField
    infer_instance
  have _ : Finite (F.Carrier ≃ₐ[K] F.Carrier) := by
    have _ : FiniteDimensional K F.Carrier :=
      Module.Finite.of_restrictScalars_finite (Padic p) K F.Carrier
    infer_instance
  change Ramification.artinConductor T.Integers (F.Carrier ≃ₐ[K] F.Carrier) _ =
    _ + Ramification.swanConductor T.Integers (F.Carrier ≃ₐ[K] F.Carrier) _
  rw [Ramification.artinConductor_eq_tame_add_swan]
  congr 2
  change fixedCodimension _ (LocalClassField.rankOneCharacterRepresentation χ)
      (lowerRamificationGroup T K 0) = _
  rw [lowerRamificationGroup_zero, fixedCodimension_rankOne]

/-- **The Artin and Swan exponents of a character are natural numbers** (from upstream's
Hasse–Arf). For every character `χ` of the automorphism group of a finite extension `F/K` of
p-adic fields, in particular of the Galois group of a finite Galois extension, the Library's
Artin and Swan expressions of its one-dimensional representation are natural numbers. -/
theorem exists_nat_artinConductor_and_swanConductor_rankOne_of_hasseArf
    (χ : (F.Carrier ≃ₐ[K] F.Carrier) →* ℂˣ) :
    (∃ a : ℕ, artinConductor T K (LocalClassField.rankOneCharacterRepresentation χ) = (a : ℚ)) ∧
    (∃ s : ℕ, swanConductor T K (LocalClassField.rankOneCharacterRepresentation χ) = (s : ℚ)) := by
  classical
  obtain ⟨m, hm⟩ := exists_finsum_lowerRamificationGroup_indicator_eq_natCast_of_hasseArf T K χ
  have hs : swanConductor T K (LocalClassField.rankOneCharacterRepresentation χ) = m := by
    rw [swanConductor_rankOne_eq_finsum, ← hm]
  refine ⟨⟨(if ∀ σ ∈ inertia T K, χ σ = 1 then 0 else 1) + m, ?_⟩, ⟨m, hs⟩⟩
  rw [artinConductor_rankOne_eq_add_swanConductor, hs, Nat.cast_add]

/-- **The rank-one case of conductor integrality** (from upstream's Hasse–Arf). For every
one-dimensional complex representation `ρ` of the automorphism group of a finite extension
`F/K` of p-adic fields, the Library's Artin and Swan expressions of `ρ` are natural numbers.
This is the conclusion of `FiniteGaloisConductorIntegralityStatement T K` for representations
of dimension one, without the Galois hypothesis. -/
theorem exists_nat_artinConductor_and_swanConductor_of_finrank_eq_one_of_hasseArf
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V) (hV : finrank ℂ V = 1) :
    (∃ a : ℕ, artinConductor T K ρ = (a : ℚ)) ∧ (∃ s : ℕ, swanConductor T K ρ = (s : ℚ)) := by
  have hsmul : ∀ g, ρ g = LinearMap.det (ρ g) • LinearMap.id := by
    intro g
    obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hV (ρ g)
    have hdet : LinearMap.det (ρ g) = c := by
      rw [hc, LinearMap.det_smul, LinearMap.det_id, hV, pow_one, mul_one]
    rw [hdet]
    exact hc
  let χ : (F.Carrier ≃ₐ[K] F.Carrier) →* ℂˣ :=
    (Units.map (LinearMap.det : (V →ₗ[ℂ] V) →* ℂ)).comp ρ.asGroupHom
  have hχ : ∀ g, (χ g : ℂ) = LinearMap.det (ρ g) := fun g => rfl
  let e : V ≃ₗ[ℂ] ℂ := LinearEquiv.ofFinrankEq V ℂ (by rw [hV, Module.finrank_self])
  let E : ρ.Equiv (LocalClassField.rankOneCharacterRepresentation χ) :=
    Representation.Equiv.mk e fun g => by
      refine LinearMap.ext fun v => ?_
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hsmul g,
        LocalClassField.rankOneCharacterRepresentation_apply, hχ, LinearMap.smul_apply,
        LinearMap.id_apply, LinearEquiv.coe_coe, map_smul, smul_eq_mul]
  obtain ⟨⟨a, ha⟩, ⟨s, hs⟩⟩ :=
    exists_nat_artinConductor_and_swanConductor_rankOne_of_hasseArf T K χ
  exact ⟨⟨a, (artinConductor_equiv T K E).trans ha⟩, ⟨s, (swanConductor_equiv T K E).trans hs⟩⟩

end Langlands.Ramification.Padic
