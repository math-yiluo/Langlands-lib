# Artin and Swan exponents: integrality for the inertia group and without the Galois hypothesis

Module `Langlands.LocalFactor.Ramification.ArtinExponent`, namespaces `Langlands.Ramification`
and `Langlands.Ramification.Padic`; auxiliary declarations in
`Langlands.Ramification.Padic.ArtinExponent`.

The integrality theorem `Padic.finiteGaloisConductorIntegrality` (module
`Langlands.LocalFactor.Ramification.FiniteIntegralityProof`) is stated for representations of the
Galois group of a Galois extension. The users of the conductor need it for representations of the
**inertia group**, which need not extend to the Galois group (the conductor of a quotient
presentation `artinConductorOfQuotient`, of a finite inertia presentation of a Weil representation,
of a Weil–Deligne representation), and they need a natural number to work with. This module
gives both, and removes the Galois hypothesis.

## Statements

**Transport.** For a local ring `R` with actions of groups `G` and `H` by ring automorphisms and
an isomorphism `e : G ≃* H` with `e g • x = g • x`, and a representation `ρ` of `H` over a field
`k` on a finite-dimensional `V`:

```lean
theorem Langlands.Ramification.artinConductor_comp_mulEquiv
    {R : Type uR} [CommRing R] [IsLocalRing R] {G : Type uG} {H : Type uH} [Group G] [Group H]
    [MulSemiringAction G R] [MulSemiringAction H R]
    {k : Type uk} [Field k] {V : Type uV} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [IsNoetherianRing R] [FaithfulSMul G R] [FaithfulSMul H R] [Finite G] [Finite H]
    (e : G ≃* H) (he : ∀ (g : G) (x : R), e g • x = g • x) (ρ : Representation k H V) :
    artinConductor R G (ρ.comp e.toMonoidHom) = artinConductor R H ρ

theorem Langlands.Ramification.swanConductor_comp_mulEquiv  -- same binders
    (e : G ≃* H) (he : ∀ (g : G) (x : R), e g • x = g • x) (ρ : Representation k H V) :
    swanConductor R G (ρ.comp e.toMonoidHom) = swanConductor R H ρ
```

with the auxiliary `mem_lowerGroup_iff_of_mulEquiv` (`e g ∈ H_i ↔ g ∈ G_i`) and
`conductorTerm_comp_mulEquiv`.

**Integrality**, for `{p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p} (T : F.TopologicalData)
(K : Type uK) [Field K] [Algebra (Padic p) K] [Algebra K F.Carrier]
[IsScalarTower (Padic p) K F.Carrier]` and `{V : Type uV} [AddCommGroup V] [Module ℂ V]
[FiniteDimensional ℂ V]`, with no Galois hypothesis:

```lean
theorem Langlands.Ramification.Padic.exists_nat_inertiaArtinConductor
    (ρ : Representation ℂ (inertia T K) V) : ∃ a : ℕ, inertiaArtinConductor T K ρ = (a : ℚ)
theorem Langlands.Ramification.Padic.exists_nat_inertiaSwanConductor
    (ρ : Representation ℂ (inertia T K) V) : ∃ s : ℕ, inertiaSwanConductor T K ρ = (s : ℚ)
theorem Langlands.Ramification.Padic.exists_nat_artinConductor
    (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V) : ∃ a : ℕ, artinConductor T K ρ = (a : ℚ)
theorem Langlands.Ramification.Padic.exists_nat_swanConductor
    (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V) : ∃ s : ℕ, swanConductor T K ρ = (s : ℚ)
theorem Langlands.Ramification.Padic.exists_nat_artinConductorOfQuotient
    {J : Type uJ} [Group J] (π : J →* inertia T K) (hπ : Function.Surjective π)
    (ρ : Representation ℂ J V) (hker : π.ker ≤ ρ.ker) :
    ∃ a : ℕ, artinConductorOfQuotient T K π hπ ρ hker = (a : ℚ)
theorem Langlands.Ramification.Padic.exists_nat_swanConductorOfQuotient  -- same binders
    : ∃ s : ℕ, swanConductorOfQuotient T K π hπ ρ hker = (s : ℚ)
```

**Exponents as definitions**, with the same variables:

```lean
def Langlands.Ramification.Padic.artinExponent
    (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V) : ℕ := ⌊artinConductor T K ρ⌋₊
def Langlands.Ramification.Padic.swanExponent
    (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V) : ℕ := ⌊swanConductor T K ρ⌋₊
def Langlands.Ramification.Padic.inertiaArtinExponent
    (ρ : Representation ℂ (inertia T K) V) : ℕ := ⌊inertiaArtinConductor T K ρ⌋₊
def Langlands.Ramification.Padic.inertiaSwanExponent
    (ρ : Representation ℂ (inertia T K) V) : ℕ := ⌊inertiaSwanConductor T K ρ⌋₊

theorem artinExponent_cast (ρ) : (artinExponent T K ρ : ℚ) = artinConductor T K ρ
theorem swanExponent_cast (ρ) : (swanExponent T K ρ : ℚ) = swanConductor T K ρ
theorem inertiaArtinExponent_cast (ρ) :
    (inertiaArtinExponent T K ρ : ℚ) = inertiaArtinConductor T K ρ
theorem inertiaSwanExponent_cast (ρ) :
    (inertiaSwanExponent T K ρ : ℚ) = inertiaSwanConductor T K ρ
theorem artinExponent_eq_fixedCodimension_add_swanExponent (ρ) :
    artinExponent T K ρ =
      fixedCodimension (F.Carrier ≃ₐ[K] F.Carrier) ρ (inertia T K) + swanExponent T K ρ
theorem inertiaArtinExponent_eq_fixedCodimension_add_inertiaSwanExponent (ρ) :
    inertiaArtinExponent T K ρ = fixedCodimension (inertia T K) ρ ⊤ + inertiaSwanExponent T K ρ
```

(all in `Langlands.Ramification.Padic`; the four `_cast` lemmas are `@[simp]`). The floor is only
a way to name the natural number; the `_cast` lemmas are the content.

## Proof outline

1. *Transport.* `e g ∈ H_i ↔ g ∈ G_i` because both conditions say `g • x − x ∈ 𝔪^{i+1}` for all
   `x` (`mem_congruenceGroup` and `he`). Hence `e` restricts to bijections `G_i ≃ H_i` (equal
   orders) and the vectors fixed by `G_i` under `ρ ∘ e` are those fixed by `H_i` under `ρ`; each
   term `conductorTerm` agrees, and so do the finite sums (`artinConductor_eq_finsum`,
   `swanConductor_eq_finsum`).
2. *Inertia.* Let `K₀ = F^I` be the fixed field of `I = inertia T K` (`inertiaField`). `F/K₀` is
   Galois (Artin's theorem, `IsGalois.of_fixed_field`), and
   `e = IntermediateField.subgroupEquivAlgEquiv I : I ≃* Gal(F/K₀)` (`inertiaEquiv`) does not
   change automorphisms of `F`, hence not their action on the integers
   (`integerAutomorphism_inertiaEquiv`). By transport,
   `inertiaArtinConductor T K ρ = artinConductor T K₀ (ρ ∘ e⁻¹)` (`inertiaArtinConductor_eq`; the
   same for Swan, `inertiaSwanConductor_eq`), and `finiteGaloisConductorIntegrality T K₀` makes
   both natural numbers.
3. *No Galois hypothesis.* The Artin and Swan expressions of a representation of
   `F.Carrier ≃ₐ[K] F.Carrier` are those of its restriction to inertia
   (`GaloisConductorInflation.artinConductor_eq_inertiaArtinConductor`,
   `GaloisConductorInflation.swanConductor_eq_inertiaSwanConductor`, module
   `Langlands.LocalFactor.Ramification.InflationProof`), so step 2 applies. The quotient forms are
   the inertia forms for the descended representation (`artinConductorOfQuotient` is by
   definition an inertia Artin expression).
4. *Exponents.* `⌊(a : ℚ)⌋₊ = a` (`Nat.floor_natCast`) gives the `_cast` lemmas; the tame
   identities are `Padic.artinConductor_eq_tame_add_swan` (module
   `Langlands.LocalFactor.Ramification.ConductorFunctional`) and the Library's
   `inertiaArtinConductor_eq_tame_add_swan` (module `Langlands.LocalFactor.Ramification.Galois`),
   cast back to `ℕ`.

## Declarations, in order

- `Ramification.mem_lowerGroup_iff_of_mulEquiv`, `conductorTerm_comp_mulEquiv`,
  `artinConductor_comp_mulEquiv`, `swanConductor_comp_mulEquiv`.
- In `Padic.ArtinExponent`: `inertiaField`, `inertiaField_isGalois`, `inertiaEquiv`,
  `integerAutomorphism_inertiaEquiv`, `inertiaArtinConductor_eq`, `inertiaSwanConductor_eq`.
- `Padic.exists_nat_inertiaArtinConductor`, `Padic.exists_nat_inertiaSwanConductor`,
  `Padic.exists_nat_artinConductor`, `Padic.exists_nat_swanConductor`,
  `Padic.exists_nat_artinConductorOfQuotient`, `Padic.exists_nat_swanConductorOfQuotient`.
- `Padic.artinExponent`, `Padic.swanExponent`, `Padic.inertiaArtinExponent`,
  `Padic.inertiaSwanExponent`, their `_cast` lemmas, and the two tame identities.

## Sources

Serre, *Local Fields* (1979), Chapter VI §2 (literature ID `serre-1979-local-fields`): the
conductor is defined through the ramification groups `G_i`, which lie in inertia, so it depends
only on the restriction to inertia (the definition before Proposition 2 and Corollary 1′, printed
pages 99–101); Theorem 1′ (page 99) is integrality. Deligne, *Les constantes des équations
fonctionnelles des fonctions L* (1973), §4.5, equation (4.5.4), printed page 538 (literature ID
`deligne-1973-local-constants`): Artin is Swan plus the codimension of the inertia invariants.
