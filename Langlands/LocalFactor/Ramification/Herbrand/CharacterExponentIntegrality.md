# Integrality of the Artin and Swan exponents of a character, from upstream's Hasse–Arf

Lean module: `Langlands.LocalFactor.Ramification.Herbrand.CharacterExponentIntegrality`
(namespace `Langlands.Ramification.Padic`). It imports
`Langlands.LocalFactor.Ramification.Herbrand.QuotientProof`,
`Langlands.LocalFactor.Ramification.RankOneArtinSum` and the ported Anthropic FLT statement module
`Langlands.LocalFactor.Ramification.HasseArf.CharacterSum`.

## What the module proves

Setting of `Ramification/FiniteStatement` and `Herbrand/Finite`: `p` a prime, `F` an actual
`PadicField` in universe `uL`, `T : F.TopologicalData` any realization, and `K : Type uK` any field
with `Algebra (Padic p) K`, `Algebra K F.Carrier` and the scalar tower (so `F/K` is finite). Write
`G = F.Carrier ≃ₐ[K] F.Carrier`, `G_i = lowerRamificationGroup T K i` (the Library's lower groups
for the action on `T.Integers`), `artinConductor T K` and `swanConductor T K` for the Library's
rational Artin and Swan expressions (the sums `Σ_{i≥0}` and `Σ_{i≥1}` of
`|G_i|/|G_0| · (dim V − dim V^{G_i})`, `Ramification/Conductor` and `Ramification/Galois`), and
`LocalClassField.rankOneCharacterRepresentation χ` for the line `ℂ` on which `g` acts by `χ g`.

**Main theorem.** For every character `χ : G →* ℂˣ`, the Artin and Swan expressions of its
one-dimensional representation are natural numbers:

```lean
theorem Langlands.Ramification.Padic.exists_nat_artinConductor_and_swanConductor_rankOne_of_hasseArf.{uK, uL}
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p} (T : F.TopologicalData) (K : Type uK)
    [Field K] [Algebra (Padic p) K] [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]
    (χ : (F.Carrier ≃ₐ[K] F.Carrier) →* ℂˣ) :
    (∃ a : ℕ, artinConductor T K (LocalClassField.rankOneCharacterRepresentation χ) = (a : ℚ)) ∧
    (∃ s : ℕ, swanConductor T K (LocalClassField.rankOneCharacterRepresentation χ) = (s : ℚ))
```

This is the conclusion of `FiniteGaloisConductorIntegralityStatement T K` for the representation of
a character, in the form of that statement. It holds for the automorphism group of every finite
extension `F/K`, so in particular for the Galois group of every finite Galois extension; the Galois
hypothesis of the Library's statement is not needed. For `K L : PadicField` as in
`Herbrand/HasseArfProof` it applies with `K := K.Carrier` and `T : L.TopologicalData`.

**Rank-one case of conductor integrality.** For every one-dimensional complex representation:

```lean
theorem Langlands.Ramification.Padic.exists_nat_artinConductor_and_swanConductor_of_finrank_eq_one_of_hasseArf.{uK, uL, uV}
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p} (T : F.TopologicalData) (K : Type uK)
    [Field K] [Algebra (Padic p) K] [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V) (hV : Module.finrank ℂ V = 1) :
    (∃ a : ℕ, artinConductor T K ρ = (a : ℚ)) ∧ (∃ s : ℕ, swanConductor T K ρ = (s : ℚ))
```

so that `fun ρ => exists_nat_artinConductor_and_swanConductor_of_finrank_eq_one_of_hasseArf T K ρ hV`
proves `FiniteGaloisConductorIntegralityStatement T K (V := V)` whenever `finrank ℂ V = 1`.

**Upstream's theorem in the Library's notions.**
`exists_finsum_lowerRamificationGroup_indicator_eq_natCast_of_hasseArf T K χ`: there is `m : ℕ` with

```lean
∑ᶠ i : ℕ, (lowerGroupOrder T K (i + 1) : ℚ) / (lowerGroupOrder T K 0 : ℚ) *
    (if ∀ σ ∈ lowerRamificationGroup T K (i + 1), χ σ = 1 then 0 else 1) = m
```

(decidability by `Classical`). The supporting identities:

- `fixedCodimension_rankOne χ H` (any group): `fixedCodimension G (rankOneCharacterRepresentation χ) H`
  is `0` if `χ` is trivial on `H` and `1` otherwise;
- `swanConductor_rankOne_eq_finsum T K χ`: the Swan expression of the character is the sum above;
- `artinConductor_rankOne_eq_add_swanConductor T K χ`: the Artin expression is the Swan expression
  plus `1` if `χ` is nontrivial on `inertia T K`, plus `0` otherwise.

### Which hypotheses of upstream's theorem are met automatically

Upstream's `Langlands.Ramification.exists_finsum_lowerGroup_indicator_eq_natCast` asks
for `R` a discrete valuation ring, `G` a finite group with a faithful `MulSemiringAction` on `R`, the
maximal ideal of `R` lying over that of `FixedPoints.subring R G`, a separable residue extension, a
perfect residue field of `R`, and a character `ψ : G →* ℂˣ`. For `R = T.Integers` and
`G = F.Carrier ≃ₐ[K] F.Carrier` with the Library's `integerAction T K`, **all of them are met
automatically**: `T.Integers` is a discrete valuation ring with finite residue field; `G` is finite
because `F/K` is finite; faithfulness is `HerbrandBridge.integerAction_faithful`; the lies-over is
`Langlands.Ramification.maximalIdeal_fixedSubring_eq_comap`; the residue field of the fixed subring embeds into the
finite residue field of `T.Integers`, so both are finite and the extension is separable and the
residue field perfect. **None remains.** Upstream's theorem needs neither commutativity of `G` (it
passes to the cyclic quotient `G ⧸ ker ψ`) nor a Galois hypothesis, and neither does this module.

## Sources

- Jean-Pierre Serre, *Local Fields*, GTM 67, Springer (1979). Registered as
  `serre-1979-local-fields`, SHA256
  `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`. Used: Chapter VI, §2 (the
  Artin representation and the integrality of its conductor, Theorems 1 and 1′, printed p. 99),
  in particular Proposition 5 and its Corollary (printed p. 102, as cited by
  `Ramification/RankOneArtinSum`): the Artin conductor of a degree-one character is `0` for the
  unit character on inertia and `φ(c) + 1` otherwise, `c` its last lower break; and Chapter IV, §3,
  the Hasse–Arf theorem (printed p. 76, proved in Chapter V, §7, Theorem 1, printed p. 93), which
  makes `φ(c)` an integer for the abelian quotient through which the character factors. Serre's
  §2 has no Swan representation; it is P. Deligne's, *Les constantes des équations fonctionnelles
  des fonctions L* (1973), §4.5, (4.5.1), printed p. 537, obtained there from Serre's
  Proposition 2.
- The proof is upstream's: the Anthropic Lean formalization of Fermat's Last Theorem
  (`github.com/anthropics/fermats-last-theorem`, commit
  `6e837e75355538c7f80bab5b956861e86c4eacc2`, registered literature
  `anthropic-flt-complete-lean-source-6e837e75`; Apache License 2.0, Copyright 2026 Anthropic,
  PBC; notices in `licenses/Anthropic-FLT/`), file
  `Theorems/Thm_IsDiscreteValuationRing_exists_finsum_lowerRamificationGroup_indicator_eq_natCast.lean`,
  theorem `Langlands.Ramification.exists_finsum_lowerGroup_indicator_eq_natCast`, with
  its import closure of 55 upstream modules, ported in `Langlands/AnthropicFLT/` (all but the
  utility module `P2M/Util.lean`). Its proof passes to `G ⧸ ker ψ`, which is cyclic, and uses the
  cyclic Hasse–Arf theorem there.
- The instance set-up for the supplied integer ring is that of `Herbrand/HasseArfProof` and
  `Herbrand/QuotientProof` (after the audit `notes/reuse/anthropic-hasse-arf-audit.md`); the count of
  fixed vectors in a line is `finrank_fixedVectors_rankOne` of `Ramification/RankOneArtinSum`.

## Proof (as implemented)

1. **Upstream's theorem for the supplied ring**
   (`exists_finsum_lowerRamificationGroup_indicator_eq_natCast_of_hasseArf`). Install
   `integerAction T K` and the topological data of `T`, and supply the hypotheses as listed above
   (explicit `Ideal.Quotient.field` structures on the two residue quotients, `Finite.of_injective`
   along the lies-over algebra map). The ported theorem then applies; its lower groups and orders
   are the Library's `lowerRamificationGroup T K i` and `lowerGroupOrder T K i` by definition.
2. **Fixed vectors in a line** (`fixedCodimension_rankOne`). `finrank_fixedVectors_rankOne` gives
   dimension `1` or `0` for the fixed vectors, and `finrank ℂ ℂ = 1`.
3. **The Swan expression** (`swanConductor_rankOne_eq_finsum`). `swanConductor T K` is by definition
   `Ramification.swanConductor T.Integers G` for the installed action (its private instance proofs
   are propositions, so any proofs give the same term); `Ramification.swanConductor_eq_finsum` writes
   it as `∑ᶠ i, conductorTerm (i + 1)`, and each term is `|G_{i+1}|/|G_0|` times the codimension of
   step 2.
4. **The Artin expression** (`artinConductor_rankOne_eq_add_swanConductor`).
   `Ramification.artinConductor_eq_tame_add_swan` splits off the codimension of the inertia
   invariants; `lowerRamificationGroup_zero` identifies `G_0` with `inertia T K`, and step 2
   evaluates the codimension.
5. **Integrality** (`exists_nat_artinConductor_and_swanConductor_rankOne_of_hasseArf`). By steps 1 and
   3 the Swan expression is the natural number `m`; by step 4 the Artin expression is
   `[χ ≠ 1 on inertia] + m`.
6. **One-dimensional representations**
   (`exists_nat_artinConductor_and_swanConductor_of_finrank_eq_one_of_hasseArf`). In dimension one
   every endomorphism is a scalar (`LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one`) and the
   scalar is its determinant (`LinearMap.det_smul`, `LinearMap.det_id`). So
   `χ := Units.map LinearMap.det ∘ ρ.asGroupHom` is a character, and a linear isomorphism
   `V ≃ₗ[ℂ] ℂ` (`LinearEquiv.ofFinrankEq`) is an equivalence of representations from `ρ` to the line
   of `χ` (`Representation.Equiv.mk`). The conductors are invariant under equivalence
   (`artinConductor_equiv`, `swanConductor_equiv` of `Ramification/Galois`), and step 5 applies.

## Relation to the planned rank-one statement

`notes/conductor-integrality.md` (section 5, gap G5) plans a theorem stating, for `F : PadicField.{u} p`,
`K : Type u` with the same instances and `[IsGalois K F.Carrier]`, and `χ : (F.Carrier ≃ₐ[K] F.Carrier) →* ℂˣ`,
that `∃ a : ℕ, artinConductor T K (LocalClassField.rankOneCharacterRepresentation χ) = (a : ℚ)`, to be
proved through local reciprocity. That statement is the first component of the main theorem here,
specialized to one universe and with an unused Galois hypothesis: given its binders, the term
`(exists_nat_artinConductor_and_swanConductor_rankOne_of_hasseArf T K χ).1` proves it (checked in a
test file). No declaration or file named in that note is created here.

## Declarations, in order

- theorem `Langlands.Ramification.Padic.fixedCodimension_rankOne`
- theorem `Langlands.Ramification.Padic.exists_finsum_lowerRamificationGroup_indicator_eq_natCast_of_hasseArf`
- theorem `Langlands.Ramification.Padic.swanConductor_rankOne_eq_finsum`
- theorem `Langlands.Ramification.Padic.artinConductor_rankOne_eq_add_swanConductor`
- theorem `Langlands.Ramification.Padic.exists_nat_artinConductor_and_swanConductor_rankOne_of_hasseArf`
- theorem `Langlands.Ramification.Padic.exists_nat_artinConductor_and_swanConductor_of_finrank_eq_one_of_hasseArf`

## Checks

Built with `lake build` on Lean 4.35.0 and Mathlib `56a0058`, without errors or warnings. All six
theorems use only the axioms `propext`, `Classical.choice` and `Quot.sound`.
