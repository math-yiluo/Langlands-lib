import Langlands.LocalFactor.Ramification.InflationStatement
import Langlands.LocalFactor.Ramification.InertiaConductorProfile
import Langlands.LocalFactor.Ramification.Herbrand.TowerProof

/-!
# Inflation from a finite Galois quotient preserves Artin and Swan sums

For a tower `K → E → L` of finite p-adic Galois extensions, the Artin and Swan sums
of a representation `ρ` of `Gal(E/K)` agree with those of its inflation `ρ ∘ π` to
`Gal(L/K)`. Both sums only involve the lower groups `G_i` with `i ≥ 0`, which lie in
inertia, so they are the sums of the restrictions to inertia. Herbrand's theorem makes
restriction carry the upper groups of `L/K` onto those of `E/K`, so the two inertia
restrictions have the same upper fixed spaces, and the published profile comparison
gives equal sums.
-/

noncomputable section

namespace Langlands.Ramification.Padic

open Module

namespace GaloisConductorInflation

universe uK uE uL uV uG uH

section FixedVectors

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Restricting a representation to a subgroup `N ⊇ H` does not change the vectors
fixed by `H`. -/
theorem fixedVectors_comp_subtype_subgroupOf {G : Type uG} [Group G]
    (ρ : Representation ℂ G V) {H N : Subgroup G} (hHN : H ≤ N) :
    fixedVectors (ρ.comp N.subtype) (H.subgroupOf N) = fixedVectors ρ H := by
  ext v
  change (∀ g : H.subgroupOf N, ρ ((g : N) : G) v = v) ↔ ∀ g : H, ρ (g : G) v = v
  constructor
  · intro hv g
    exact hv ⟨⟨g, hHN g.property⟩, Subgroup.mem_subgroupOf.mpr g.property⟩
  · intro hv g
    exact hv ⟨(g : N), Subgroup.mem_subgroupOf.mp g.property⟩

/-- The vectors fixed by `H` acting through `f` are those fixed by the image `f(H)`. -/
theorem fixedVectors_comp_map {G : Type uG} [Group G] {G' : Type uH} [Group G']
    (ρ : Representation ℂ G V) (f : G' →* G) (H : Subgroup G') :
    fixedVectors (ρ.comp f) H = fixedVectors ρ (H.map f) := by
  ext v
  change (∀ h : H, ρ (f h) v = v) ↔ ∀ g : H.map f, ρ (g : G) v = v
  constructor
  · rintro hv ⟨g, hg⟩
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hg
    exact hv ⟨h, hh⟩
  · intro hv h
    exact hv ⟨f h, Subgroup.mem_map_of_mem f h.property⟩

end FixedVectors

section Restriction

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
  (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
  [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

private theorem integerAction_faithful :
    letI := integerAction T K
    FaithfulSMul (F.Carrier ≃ₐ[K] F.Carrier) T.Integers := by
  let := integerAction T K
  let := T.valuativeRel
  have : IsFractionRing T.Integers F.Carrier :=
    inferInstanceAs (IsFractionRing
      (ValuativeRel.valuation F.Carrier).valuationSubring F.Carrier)
  refine ⟨fun {σ τ} h => ?_⟩
  have heq : σ.toRingHom = τ.toRingHom :=
    IsFractionRing.ringHom_ext (A := T.Integers) (fun x =>
      congrArg (fun y : T.Integers => (y : F.Carrier)) (h x))
  exact AlgEquiv.ext fun x => RingHom.congr_fun heq x

private theorem inertiaAction_faithful :
    letI := inertiaIntegerAction T K
    FaithfulSMul (inertia T K) T.Integers := by
  let := inertiaIntegerAction T K
  let := T.valuativeRel
  have : IsFractionRing T.Integers F.Carrier :=
    inferInstanceAs (IsFractionRing
      (ValuativeRel.valuation F.Carrier).valuationSubring F.Carrier)
  refine ⟨fun {σ τ} h => Subtype.ext ?_⟩
  have heq : (σ : F.Carrier ≃ₐ[K] F.Carrier).toRingHom =
      (τ : F.Carrier ≃ₐ[K] F.Carrier).toRingHom :=
    IsFractionRing.ringHom_ext (A := T.Integers) (fun x =>
      congrArg (fun y : T.Integers => (y : F.Carrier)) (h x))
  exact AlgEquiv.ext fun x => RingHom.congr_fun heq x

private theorem integers_isNoetherianRing : IsNoetherianRing T.Integers := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

private theorem automorphisms_finite : Finite (F.Carrier ≃ₐ[K] F.Carrier) := by
  have : FiniteDimensional K F.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) K F.Carrier
  infer_instance

/-- Every lower group `G_i`, `i ≥ 0`, lies in inertia. -/
theorem lowerRamificationGroup_le_inertia (i : ℕ) :
    lowerRamificationGroup T K i ≤ inertia T K := by
  rw [← lowerRamificationGroup_zero T K]
  exact lowerRamificationGroup_antitone T K (Nat.zero_le i)

/-- The Galois-group Artin sum, with its terms written out. -/
theorem artinConductor_eq_finsum (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V) :
    artinConductor T K ρ = ∑ᶠ i : ℕ,
      (lowerGroupOrder T K i : ℚ) / lowerGroupOrder T K 0 *
        fixedCodimension (F.Carrier ≃ₐ[K] F.Carrier) ρ (lowerRamificationGroup T K i) := by
  let := integerAction T K
  have := integerAction_faithful T K
  have := integers_isNoetherianRing T
  have := automorphisms_finite (F := F) K
  change Ramification.artinConductor T.Integers (F.Carrier ≃ₐ[K] F.Carrier) ρ = _
  rw [Ramification.artinConductor_eq_finsum]
  rfl

/-- The Galois-group Swan sum, with its terms written out. -/
theorem swanConductor_eq_finsum (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V) :
    swanConductor T K ρ = ∑ᶠ i : ℕ,
      (lowerGroupOrder T K (i + 1) : ℚ) / lowerGroupOrder T K 0 *
        fixedCodimension (F.Carrier ≃ₐ[K] F.Carrier) ρ
          (lowerRamificationGroup T K (i + 1)) := by
  let := integerAction T K
  have := integerAction_faithful T K
  have := integers_isNoetherianRing T
  have := automorphisms_finite (F := F) K
  change Ramification.swanConductor T.Integers (F.Carrier ≃ₐ[K] F.Carrier) ρ = _
  rw [Ramification.swanConductor_eq_finsum]
  rfl

/-- The inertia Artin sum, with its terms written out. -/
theorem inertiaArtinConductor_eq_finsum (ρ : Representation ℂ (inertia T K) V) :
    inertiaArtinConductor T K ρ = ∑ᶠ i : ℕ,
      (Nat.card (inertiaLowerGroup T K i) : ℚ) / Nat.card (inertiaLowerGroup T K 0) *
        fixedCodimension (inertia T K) ρ (inertiaLowerGroup T K i) := by
  let := inertiaIntegerAction T K
  have := inertiaAction_faithful T K
  have := integers_isNoetherianRing T
  have := automorphisms_finite (F := F) K
  change Ramification.artinConductor T.Integers (inertia T K) ρ = _
  rw [Ramification.artinConductor_eq_finsum]
  rfl

/-- The inertia Swan sum, with its terms written out. -/
theorem inertiaSwanConductor_eq_finsum (ρ : Representation ℂ (inertia T K) V) :
    inertiaSwanConductor T K ρ = ∑ᶠ i : ℕ,
      (Nat.card (inertiaLowerGroup T K (i + 1)) : ℚ) / Nat.card (inertiaLowerGroup T K 0) *
        fixedCodimension (inertia T K) ρ (inertiaLowerGroup T K (i + 1)) := by
  let := inertiaIntegerAction T K
  have := inertiaAction_faithful T K
  have := integers_isNoetherianRing T
  have := automorphisms_finite (F := F) K
  change Ramification.swanConductor T.Integers (inertia T K) ρ = _
  rw [Ramification.swanConductor_eq_finsum]
  rfl

/-- The fixed-space codimension of a lower group is unchanged by restriction to inertia. -/
theorem fixedCodimension_inertiaLowerGroup
    (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V) (i : ℕ) :
    fixedCodimension (inertia T K) (ρ.comp (inertia T K).subtype) (inertiaLowerGroup T K i) =
      fixedCodimension (F.Carrier ≃ₐ[K] F.Carrier) ρ (lowerRamificationGroup T K i) := by
  unfold fixedCodimension
  rw [inertiaLowerGroup,
    fixedVectors_comp_subtype_subgroupOf ρ (lowerRamificationGroup_le_inertia T K i)]

/-- The Artin sum of a Galois representation is that of its restriction to inertia. -/
theorem artinConductor_eq_inertiaArtinConductor
    (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V) :
    artinConductor T K ρ = inertiaArtinConductor T K (ρ.comp (inertia T K).subtype) := by
  rw [artinConductor_eq_finsum, inertiaArtinConductor_eq_finsum]
  refine finsum_congr fun i => ?_
  rw [card_inertiaLowerGroup, card_inertiaLowerGroup, fixedCodimension_inertiaLowerGroup]

/-- The Swan sum of a Galois representation is that of its restriction to inertia. -/
theorem swanConductor_eq_inertiaSwanConductor
    (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V) :
    swanConductor T K ρ = inertiaSwanConductor T K (ρ.comp (inertia T K).subtype) := by
  rw [swanConductor_eq_finsum, inertiaSwanConductor_eq_finsum]
  refine finsum_congr fun i => ?_
  rw [card_inertiaLowerGroup, card_inertiaLowerGroup, fixedCodimension_inertiaLowerGroup]

/-- For `v ≥ 0` the upper group `G^v` lies in inertia. -/
theorem upperRamificationGroup_le_inertia {v : ℝ} (hv : 0 ≤ v) :
    upperRamificationGroup T K v ≤ inertia T K := by
  rw [← upperRamificationGroup_zero T K]
  exact upperRamificationGroup_antitone T K hv

omit [FiniteDimensional ℂ V] in
/-- For `v ≥ 0` the upper fixed space of the restriction to inertia is the space fixed
by the upper group `G^v` itself. -/
theorem inertiaUpperFixedVectors_comp_subtype
    (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V) {v : ℝ} (hv : 0 ≤ v) :
    inertiaUpperFixedVectors T K (ρ.comp (inertia T K).subtype) v =
      fixedVectors ρ (upperRamificationGroup T K v) :=
  fixedVectors_comp_subtype_subgroupOf ρ (upperRamificationGroup_le_inertia T K hv)

end Restriction

section Tower

variable {p : ℕ} [Fact p.Prime] {E : PadicField.{uE} p} {L : PadicField.{uL} p}
  (TE : E.TopologicalData) (TL : L.TopologicalData)
  (K : Type uK) [Field K] [Algebra (Padic p) K]
  [Algebra K E.Carrier] [Algebra K L.Carrier] [Algebra E.Carrier L.Carrier]
  [IsScalarTower (Padic p) K E.Carrier] [IsScalarTower (Padic p) K L.Carrier]
  [IsScalarTower K E.Carrier L.Carrier]

/-- Herbrand's theorem for a base field that is not packaged as a `PadicField`:
restriction maps every upper group of `L/K` onto the upper group of `E/K` with the
same index. -/
theorem map_upperRamificationGroup [IsGalois K E.Carrier] [IsGalois K L.Carrier]
    (v : ℝ) (hv : -1 ≤ v) :
    (upperRamificationGroup TL K v).map
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := L.Carrier) E.Carrier) =
      upperRamificationGroup TE K v := by
  have : FiniteDimensional (Padic p) K :=
    FiniteDimensional.of_injective (IsScalarTower.toAlgHom (Padic p) K E.Carrier).toLinearMap
      (fun x y h => (algebraMap K E.Carrier).injective h)
  have : IsGalois E.Carrier L.Carrier := IsGalois.tower_top_of_isGalois K E.Carrier L.Carrier
  let K' : PadicField.{uK} p := PadicField.ofField K
  let : Algebra K'.Carrier L.Carrier := ‹Algebra K L.Carrier›
  let : Algebra K'.Carrier E.Carrier := ‹Algebra K E.Carrier›
  have : IsScalarTower (Padic p) K'.Carrier L.Carrier := ‹IsScalarTower (Padic p) K L.Carrier›
  have : IsScalarTower (Padic p) K'.Carrier E.Carrier := ‹IsScalarTower (Padic p) K E.Carrier›
  have : IsScalarTower K'.Carrier E.Carrier L.Carrier := ‹IsScalarTower K E.Carrier L.Carrier›
  have : IsGalois K'.Carrier L.Carrier := ‹IsGalois K L.Carrier›
  have : IsGalois K'.Carrier E.Carrier := ‹IsGalois K E.Carrier›
  exact HerbrandBridge.upperRestrictionCompatibility K' L E TL TE v hv

end Tower

end GaloisConductorInflation

open GaloisConductorInflation

universe uK uE uL uV

/-- Serre, *Local Fields*, VI §2, Proposition 3 and its Corollary, for the actual
rational Artin and Swan sums: inflation from `Gal(E/K)` to `Gal(L/K)` preserves both. -/
theorem finiteGaloisConductorInflation
    {p : ℕ} [Fact p.Prime] {E : PadicField.{uE} p} {L : PadicField.{uL} p}
    (TE : E.TopologicalData) (TL : L.TopologicalData)
    (K : Type uK) [Field K] [Algebra (Padic p) K]
    [Algebra K E.Carrier] [Algebra K L.Carrier] [Algebra E.Carrier L.Carrier]
    [IsScalarTower (Padic p) K E.Carrier] [IsScalarTower (Padic p) K L.Carrier]
    [IsScalarTower (Padic p) E.Carrier L.Carrier] [IsScalarTower K E.Carrier L.Carrier]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] :
    FiniteGaloisConductorInflationStatement TE TL K (V := V) := by
  intro _ _ ρ π
  have hfix : ∀ v : ℝ, 0 ≤ v →
      inertiaUpperFixedVectors TL K ((ρ.comp π).comp (inertia TL K).subtype) v =
        inertiaUpperFixedVectors TE K (ρ.comp (inertia TE K).subtype) v := by
    intro v hv
    rw [inertiaUpperFixedVectors_comp_subtype TL K (ρ.comp π) hv,
      inertiaUpperFixedVectors_comp_subtype TE K ρ hv, fixedVectors_comp_map,
      map_upperRamificationGroup TE TL K v (by linarith)]
  obtain ⟨hA, hS⟩ := inertiaConductors_eq_of_upperFixedDimension TE TL K
    (ρ.comp (inertia TE K).subtype) ((ρ.comp π).comp (inertia TL K).subtype)
    (fun v hv => by rw [hfix v hv])
  refine ⟨?_, ?_⟩
  · rw [artinConductor_eq_inertiaArtinConductor TL K, artinConductor_eq_inertiaArtinConductor TE K]
    exact hA
  · rw [swanConductor_eq_inertiaSwanConductor TL K, swanConductor_eq_inertiaSwanConductor TE K]
    exact hS

end Langlands.Ramification.Padic
