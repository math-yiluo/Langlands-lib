import Langlands.LocalFactor.Ramification.FiniteIntegralityProof
import Langlands.LocalFactor.Ramification.InflationProof

/-!
# Artin and Swan exponents: integrality for the inertia group and without the Galois hypothesis

The Artin and Swan expressions depend only on the group with its action on the ring
(`Ramification.artinConductor_comp_mulEquiv`, `Ramification.swanConductor_comp_mulEquiv`).
The inertia group `I = inertia T K` of a finite extension `F/K` of p-adic fields, with its action
on the integers of `F`, is the Galois group of `F` over the fixed field `K₀ = F^I` with its
action, and `F/K₀` is Galois. So the integrality theorem
`Padic.finiteGaloisConductorIntegrality` applies over `K₀`: for every finite-dimensional complex
representation of the inertia group, the inertia Artin and Swan expressions are natural numbers
(`Padic.exists_nat_inertiaArtinConductor`, `Padic.exists_nat_inertiaSwanConductor`). Since the
expressions of a representation of `Gal(F/K)` are those of its restriction to inertia, they are
natural numbers without the Galois hypothesis (`Padic.exists_nat_artinConductor`,
`Padic.exists_nat_swanConductor`). The natural numbers are named as definitions
(`Padic.artinExponent`, `Padic.swanExponent`, `Padic.inertiaArtinExponent`,
`Padic.inertiaSwanExponent`).
-/

noncomputable section

namespace Langlands.Ramification

open Module

universe uR uG uH uk uV uK uL uJ

section Transport

variable {R : Type uR} [CommRing R] [IsLocalRing R] {G : Type uG} {H : Type uH} [Group G]
  [Group H] [MulSemiringAction G R] [MulSemiringAction H R]
  {k : Type uk} [Field k] {V : Type uV} [AddCommGroup V] [Module k V]

/-- An isomorphism compatible with the actions matches the lower groups. -/
theorem mem_lowerGroup_iff_of_mulEquiv (e : G ≃* H) (he : ∀ (g : G) (x : R), e g • x = g • x)
    (i : ℕ) (g : G) : e g ∈ lowerGroup R H i ↔ g ∈ lowerGroup R G i := by
  simp only [lowerGroup, mem_congruenceGroup, he]

variable [FiniteDimensional k V]

theorem conductorTerm_comp_mulEquiv (e : G ≃* H) (he : ∀ (g : G) (x : R), e g • x = g • x)
    (ρ : Representation k H V) (i : ℕ) :
    conductorTerm R G (ρ.comp e.toMonoidHom) i = conductorTerm R H ρ i := by
  have hcard (j : ℕ) : Nat.card (lowerGroup R G j) = Nat.card (lowerGroup R H j) :=
    Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun g =>
      (mem_lowerGroup_iff_of_mulEquiv e he j g).symm)
  have hfix : fixedVectors (ρ.comp e.toMonoidHom) (lowerGroup R G i) =
      fixedVectors ρ (lowerGroup R H i) := by
    ext v
    change (∀ g : lowerGroup R G i, ρ (e g) v = v) ↔ (∀ h : lowerGroup R H i, ρ h v = v)
    constructor
    · intro hv h
      obtain ⟨g, hg⟩ := e.surjective h
      have hgi : g ∈ lowerGroup R G i := by
        rw [← mem_lowerGroup_iff_of_mulEquiv e he, hg]
        exact h.2
      have := hv ⟨g, hgi⟩
      rwa [show e g = h from hg] at this
    · intro hv g
      exact hv ⟨e g, (mem_lowerGroup_iff_of_mulEquiv e he i g).mpr g.2⟩
  simp only [conductorTerm, fixedCodimension, hcard]
  rw [hfix]

variable [IsNoetherianRing R] [FaithfulSMul G R] [FaithfulSMul H R] [Finite G] [Finite H]

/-- **The Artin expression depends only on the group with its action on the ring.** -/
theorem artinConductor_comp_mulEquiv (e : G ≃* H) (he : ∀ (g : G) (x : R), e g • x = g • x)
    (ρ : Representation k H V) :
    artinConductor R G (ρ.comp e.toMonoidHom) = artinConductor R H ρ := by
  rw [artinConductor_eq_finsum, artinConductor_eq_finsum]
  exact finsum_congr fun i => conductorTerm_comp_mulEquiv e he ρ i

/-- **The Swan expression depends only on the group with its action on the ring.** -/
theorem swanConductor_comp_mulEquiv (e : G ≃* H) (he : ∀ (g : G) (x : R), e g • x = g • x)
    (ρ : Representation k H V) :
    swanConductor R G (ρ.comp e.toMonoidHom) = swanConductor R H ρ := by
  rw [swanConductor_eq_finsum, swanConductor_eq_finsum]
  exact finsum_congr fun i => conductorTerm_comp_mulEquiv e he ρ (i + 1)

end Transport

namespace Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
  (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
  [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]

namespace ArtinExponent

/-- The fixed field `K₀ = F^I` of the inertia group. -/
abbrev inertiaField : IntermediateField K F.Carrier := IntermediateField.fixedField (inertia T K)

theorem inertiaField_isGalois : IsGalois (inertiaField T K) F.Carrier := by
  have := LocalFactor.SpectralConductor.automorphismGroup_finite' (E := F) K
  exact IsGalois.of_fixed_field F.Carrier (inertia T K)

/-- The inertia group as the Galois group of `F` over the fixed field of inertia. -/
def inertiaEquiv : inertia T K ≃* (F.Carrier ≃ₐ[inertiaField T K] F.Carrier) :=
  haveI : FiniteDimensional K F.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) K F.Carrier
  IntermediateField.subgroupEquivAlgEquiv (inertia T K)

/-- The isomorphism does not change the action on the integers. -/
theorem integerAutomorphism_inertiaEquiv (σ : inertia T K) (x : T.Integers) :
    integerAutomorphism T (inertiaField T K) (inertiaEquiv T K σ) x =
      integerAutomorphism T K σ x :=
  Subtype.ext rfl

variable {k : Type uk} [Field k] {V : Type uV} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

/-- The inertia Artin expression is the Artin expression over the fixed field of inertia. -/
theorem inertiaArtinConductor_eq (ρ : Representation k (inertia T K) V) :
    inertiaArtinConductor T K ρ =
      artinConductor T (inertiaField T K) (ρ.comp (inertiaEquiv T K).symm.toMonoidHom) := by
  let := inertiaIntegerAction T K
  let := integerAction T (inertiaField T K)
  have := LocalFactor.SpectralConductor.inertiaIntegerAction_faithful' T K
  have := HerbrandBridge.integerAction_faithful T (inertiaField T K)
  have := LocalFactor.SpectralConductor.integerRing_noetherian' T
  have := LocalFactor.SpectralConductor.automorphismGroup_finite' (E := F) K
  have := LocalFactor.SpectralConductor.automorphismGroup_finite' (E := F) (inertiaField T K)
  change Ramification.artinConductor T.Integers (inertia T K) ρ =
    Ramification.artinConductor T.Integers _ (ρ.comp (inertiaEquiv T K).symm.toMonoidHom)
  have hρ : (ρ.comp (inertiaEquiv T K).symm.toMonoidHom).comp (inertiaEquiv T K).toMonoidHom =
      ρ := by
    ext σ
    simp
  conv_lhs => rw [← hρ]
  exact artinConductor_comp_mulEquiv (inertiaEquiv T K)
    (fun σ x => integerAutomorphism_inertiaEquiv T K σ x) _

/-- The inertia Swan expression is the Swan expression over the fixed field of inertia. -/
theorem inertiaSwanConductor_eq (ρ : Representation k (inertia T K) V) :
    inertiaSwanConductor T K ρ =
      swanConductor T (inertiaField T K) (ρ.comp (inertiaEquiv T K).symm.toMonoidHom) := by
  let := inertiaIntegerAction T K
  let := integerAction T (inertiaField T K)
  have := LocalFactor.SpectralConductor.inertiaIntegerAction_faithful' T K
  have := HerbrandBridge.integerAction_faithful T (inertiaField T K)
  have := LocalFactor.SpectralConductor.integerRing_noetherian' T
  have := LocalFactor.SpectralConductor.automorphismGroup_finite' (E := F) K
  have := LocalFactor.SpectralConductor.automorphismGroup_finite' (E := F) (inertiaField T K)
  change Ramification.swanConductor T.Integers (inertia T K) ρ =
    Ramification.swanConductor T.Integers _ (ρ.comp (inertiaEquiv T K).symm.toMonoidHom)
  have hρ : (ρ.comp (inertiaEquiv T K).symm.toMonoidHom).comp (inertiaEquiv T K).toMonoidHom =
      ρ := by
    ext σ
    simp
  conv_lhs => rw [← hρ]
  exact swanConductor_comp_mulEquiv (inertiaEquiv T K)
    (fun σ x => integerAutomorphism_inertiaEquiv T K σ x) _

end ArtinExponent

open ArtinExponent

section Integrality

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- **The inertia Artin expression is a natural number**, for every finite-dimensional complex
representation of the inertia group (which need not extend to the Galois group). -/
theorem exists_nat_inertiaArtinConductor (ρ : Representation ℂ (inertia T K) V) :
    ∃ a : ℕ, inertiaArtinConductor T K ρ = (a : ℚ) := by
  have := inertiaField_isGalois T K
  rw [inertiaArtinConductor_eq]
  exact (finiteGaloisConductorIntegrality T (inertiaField T K) _).1

/-- **The inertia Swan expression is a natural number.** -/
theorem exists_nat_inertiaSwanConductor (ρ : Representation ℂ (inertia T K) V) :
    ∃ s : ℕ, inertiaSwanConductor T K ρ = (s : ℚ) := by
  have := inertiaField_isGalois T K
  rw [inertiaSwanConductor_eq]
  exact (finiteGaloisConductorIntegrality T (inertiaField T K) _).2

/-- **Integrality without the Galois hypothesis**: the Artin expression of a representation of
the automorphism group of any finite extension of p-adic fields is a natural number. -/
theorem exists_nat_artinConductor (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V) :
    ∃ a : ℕ, artinConductor T K ρ = (a : ℚ) := by
  rw [GaloisConductorInflation.artinConductor_eq_inertiaArtinConductor]
  exact exists_nat_inertiaArtinConductor T K _

/-- The Swan expression of a representation of the automorphism group of any finite extension of
p-adic fields is a natural number. -/
theorem exists_nat_swanConductor (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V) :
    ∃ s : ℕ, swanConductor T K ρ = (s : ℚ) := by
  rw [GaloisConductorInflation.swanConductor_eq_inertiaSwanConductor]
  exact exists_nat_inertiaSwanConductor T K _

/-- The Artin expression of an explicit finite inertia quotient is a natural number. -/
theorem exists_nat_artinConductorOfQuotient {J : Type uJ} [Group J] (π : J →* inertia T K)
    (hπ : Function.Surjective π) (ρ : Representation ℂ J V) (hker : π.ker ≤ ρ.ker) :
    ∃ a : ℕ, artinConductorOfQuotient T K π hπ ρ hker = (a : ℚ) :=
  exists_nat_inertiaArtinConductor T K _

/-- The Swan expression of an explicit finite inertia quotient is a natural number. -/
theorem exists_nat_swanConductorOfQuotient {J : Type uJ} [Group J] (π : J →* inertia T K)
    (hπ : Function.Surjective π) (ρ : Representation ℂ J V) (hker : π.ker ≤ ρ.ker) :
    ∃ s : ℕ, swanConductorOfQuotient T K π hπ ρ hker = (s : ℚ) :=
  exists_nat_inertiaSwanConductor T K _

end Integrality

section Exponents

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The Artin exponent: the Artin expression as a natural number. -/
def artinExponent (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V) : ℕ :=
  ⌊artinConductor T K ρ⌋₊

/-- The Swan exponent: the Swan expression as a natural number. -/
def swanExponent (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V) : ℕ :=
  ⌊swanConductor T K ρ⌋₊

/-- The Artin exponent of a representation of the inertia group. -/
def inertiaArtinExponent (ρ : Representation ℂ (inertia T K) V) : ℕ :=
  ⌊inertiaArtinConductor T K ρ⌋₊

/-- The Swan exponent of a representation of the inertia group. -/
def inertiaSwanExponent (ρ : Representation ℂ (inertia T K) V) : ℕ :=
  ⌊inertiaSwanConductor T K ρ⌋₊

@[simp]
theorem artinExponent_cast (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V) :
    (artinExponent T K ρ : ℚ) = artinConductor T K ρ := by
  obtain ⟨a, ha⟩ := exists_nat_artinConductor T K ρ
  rw [artinExponent, ha, Nat.floor_natCast]

@[simp]
theorem swanExponent_cast (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V) :
    (swanExponent T K ρ : ℚ) = swanConductor T K ρ := by
  obtain ⟨s, hs⟩ := exists_nat_swanConductor T K ρ
  rw [swanExponent, hs, Nat.floor_natCast]

@[simp]
theorem inertiaArtinExponent_cast (ρ : Representation ℂ (inertia T K) V) :
    (inertiaArtinExponent T K ρ : ℚ) = inertiaArtinConductor T K ρ := by
  obtain ⟨a, ha⟩ := exists_nat_inertiaArtinConductor T K ρ
  rw [inertiaArtinExponent, ha, Nat.floor_natCast]

@[simp]
theorem inertiaSwanExponent_cast (ρ : Representation ℂ (inertia T K) V) :
    (inertiaSwanExponent T K ρ : ℚ) = inertiaSwanConductor T K ρ := by
  obtain ⟨s, hs⟩ := exists_nat_inertiaSwanConductor T K ρ
  rw [inertiaSwanExponent, hs, Nat.floor_natCast]

/-- The Artin exponent is the codimension of the inertia invariants plus the Swan exponent. -/
theorem artinExponent_eq_fixedCodimension_add_swanExponent
    (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V) :
    artinExponent T K ρ =
      fixedCodimension (F.Carrier ≃ₐ[K] F.Carrier) ρ (inertia T K) + swanExponent T K ρ := by
  have h := Langlands.Ramification.Padic.artinConductor_eq_tame_add_swan T K ρ
  rw [← artinExponent_cast, ← swanExponent_cast] at h
  exact_mod_cast h

/-- The inertia Artin exponent is the codimension of the invariants plus the inertia Swan
exponent. -/
theorem inertiaArtinExponent_eq_fixedCodimension_add_inertiaSwanExponent
    (ρ : Representation ℂ (inertia T K) V) :
    inertiaArtinExponent T K ρ =
      fixedCodimension (inertia T K) ρ ⊤ + inertiaSwanExponent T K ρ := by
  have h := inertiaArtinConductor_eq_tame_add_swan T K ρ
  rw [← inertiaArtinExponent_cast, ← inertiaSwanExponent_cast] at h
  exact_mod_cast h

end Exponents

end Padic

end Langlands.Ramification
