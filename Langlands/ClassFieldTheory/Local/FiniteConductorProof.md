# Finite-character conductor transport under local reciprocity: proof

The module `Langlands.ClassFieldTheory.Local.FiniteConductorProof` proves the
published proposition
`Langlands.LocalClassField.FiniteCharacterConductorTheorems.{u}` with the theorem

```lean
theorem Langlands.LocalClassField.finiteCharacterConductorTheorems :
    FiniteCharacterConductorTheorems.{u}
```

Its type is exactly the target, at an arbitrary universe level `u`. The target is
defined in [`FiniteConductorStatement`](FiniteConductorStatement.lean), which the
module imports by its Lean name. The module changes neither that statement nor
anything it imports. It adds no hypothesis: every clause holds for every prime `p`,
p-adic field `F : PadicField.{u} p`, topological data `T`, continuous homomorphism
`r` satisfying `GeometricProfiniteReciprocityRelation F T r`, finite abelian
extension `L` with topological data `S`, character `χ` and level `n`, exactly as
quantified by the target.

## What is proved

The target is the conjunction of five propositions, explained in full in
[`FiniteConductorStatement.md`](FiniteConductorStatement.md). Write `G` for the
actual Galois group of `L/F`, `G_i` for its lower and `G^v` for its upper
ramification groups (`lowerRamificationGroup S F.Carrier i`,
`upperRamificationGroup S F.Carrier v`), `φ` for Herbrand's function
`herbrandPhi S F.Carrier`, `U^(n)` for `T.unitFiltration n`, and `a(χ ∘ r)` for the
multiplicative conductor `T.multiplicativeConductor (χ.comp (finiteFamilyOfHom r L))`.

1. `UnitFiltrationComparison`: `U^(n)` equals the principal units `T.principalUnits n`.
2. `FiniteReciprocityInertiaImages`: `r` maps `T.unitSubgroup` onto the inertia
   group `inertia S F.Carrier` and `U^(1)` onto `G_1`.
3. `FiniteReciprocityConductorTransport`: `a(χ ∘ r)`, as a rational number, equals
   the Artin expression `Ramification.Padic.artinConductor S F.Carrier` of the
   one-dimensional representation `rankOneCharacterRepresentation χ` of `G`.
4. `FiniteReciprocityConductorLevels`: that Artin expression is at most `n` exactly
   when `χ ∘ r` is trivial on `U^(n)`.
5. `FiniteReciprocityUnramifiedTameCharacters`: `a(χ ∘ r) = 0` exactly when `χ` is
   trivial on inertia, and `a(χ ∘ r) ≤ 1` exactly when `χ` is trivial on `G_1`.

## Published results used

- `LocalClassField.finiteUpperReciprocityTheorems.{u}` (module
  `Langlands.ClassFieldTheory.Local.UpperReciprocityProof`) proves
  `FiniteUpperReciprocityTheorems.{u}` under the same hypotheses as the target. Three
  of its conjuncts are used:
  - `FiniteReciprocityHigherUnitImages`: `r(U^(n)) = G^n` for every `n : ℕ`;
  - `FiniteReciprocityRealUnitImages`: `r(U^(⌈v⌉)) = G^v` for every real `v ≥ 0`;
  - `FiniteCharacterUpperConductorLevels`: for every real `v ≥ 0`,
    `a(χ ∘ r) ≤ ⌈v⌉` exactly when `χ` is trivial on `G^v`.
- `LocalClassField.unitFiltrationComparison` and
  `PadicField.TopologicalData.multiplicativeConductor_le_iff_unitFiltration_le_ker`
  (module `Langlands.ClassFieldTheory.Local.UnitFiltrationConductor`): clause 1, and
  `T.multiplicativeConductor ψ ≤ n ↔ U^(n) ≤ ker ψ` for a continuous character `ψ`
  of `F.Carrierˣ`.
- `PadicField.TopologicalData.unitFiltration_zero` (module
  `Langlands.ClassFieldTheory.Local.UnitFiltrationStructuralProof`):
  `U^(0) = T.unitSubgroup`.
- From `Langlands.LocalFactor.Ramification.Herbrand.Finite`:
  `upperRamificationGroup_zero` (`G^0` is inertia), `upperRamificationGroup_phi`
  (`G^(φ(u))` is the real-indexed lower group at `u`),
  `lowerRamificationGroupReal_nat` (at a natural number it is `G_i`),
  `upperRamificationGroup_antitone`, `herbrandPhi_pos`, `lowerGroupOrder` (the order
  of `G_i`) and `lowerGroupOrder_pos`.
- `herbrandPhi_natCast` (module
  `Langlands.LocalFactor.Ramification.InertiaConductorProfile`):
  `φ(i) = (Σ_(k<i) |G_(k+1)|) / |G_0|` for a natural number `i`.
- From `Langlands.LocalFactor.Ramification.Galois`: `inertia`,
  `lowerRamificationGroup_zero` (`G_0` is inertia), `lowerRamificationGroup_antitone`,
  `exists_lowerRamificationGroup_eq_bot` (the lower groups vanish from some index
  on), the integer actions `integerAction` and `inertiaIntegerAction`, the lower
  groups of inertia `inertiaLowerGroup`, and the definitions `artinConductor` and
  `inertiaArtinConductor`, which apply the abstract Artin expression
  `Ramification.artinConductor` to these actions.
- `Ramification.artinConductor_eq_sum_range` (module
  `Langlands.LocalFactor.Ramification.Conductor`): the abstract Artin expression is
  the finite sum of `conductorTerm`, `|G_i| / |G_0|` times the codimension of the
  `G_i`-fixed vectors, over the indices below any bound beyond which the lower groups
  vanish.
- `inertiaArtinConductor_rankOne_eq_of_upper_levels` (module
  `Langlands.LocalFactor.Ramification.RankOneArtinSum`): if a character `ρ` of inertia
  is trivial on `G^s` (meaning on the elements of inertia lying in `G^s`) exactly when
  `a ≤ ⌈s⌉`, for every real `s ≥ 0`, then the inertia Artin expression of its
  one-dimensional representation is `a`. This is the rank-one case of Serre,
  *Local Fields*, VI §2, Proposition 5.

## Auxiliary results of the module

All are in namespace `Langlands.Ramification.Padic` and are stated for an actual
finite extension `F.Carrier/K` with topological data `T`, as in the module `Galois`.

- `herbrandPhi_one_mem_Ioc`: `0 < φ(1) ≤ 1`. Positivity is `herbrandPhi_pos`; by
  `herbrandPhi_natCast`, `φ(1) = |G_1| / |G_0|`, and `|G_1| ≤ |G_0|` because
  `G_1 ≤ G_0` (`lowerRamificationGroup_antitone`, `Subgroup.card_le_of_le`).
- `natCeil_herbrandPhi_one`: `⌈φ(1)⌉ = 1`, by `Nat.ceil_eq_iff` from the previous
  item.
- `upperRamificationGroup_herbrandPhi_one`: `G^(φ(1)) = G_1`, by
  `upperRamificationGroup_phi` and `lowerRamificationGroupReal_nat`.
- `upperRamificationGroup_le_inertia` and `lowerRamificationGroup_le_inertia`:
  `G^v` (for `v ≥ 0`) and `G_i` lie in inertia, by antitonicity from `G^0` and `G_0`,
  which are inertia.
- `Langlands.Ramification.HerbrandBridge.integerAction_faithful`, `inertiaIntegerAction_faithfulSMul`,
  `integers_isNoetherianRing`, `automorphismGroup_finite_of_padic`: the instance
  facts used by `artinConductor` and `inertiaArtinConductor`. The module `Galois`
  proves them as private lemmas, so they are reproved here by the same arguments:
  an automorphism is determined by its action on the integers, since `F.Carrier` is
  their fraction field; inertia inherits faithfulness; the integer ring of a local
  field is Noetherian; and the automorphism group of a finite extension is finite.
- `fixedVectors_comp_subtype_subgroupOf`: for subgroups `H ≤ I` of a group and a
  representation `ρ`, the vectors fixed by `H`, regarded as a subgroup of `I`, under
  the restriction of `ρ` to `I` are the vectors fixed by `H` under `ρ`.
- `artinConductor_eq_sum_range_lower` and `inertiaArtinConductor_eq_sum_range_lower`:
  `artinConductor T K ρ` and `inertiaArtinConductor T K ρ` written as the finite sums
  of `Ramification.artinConductor_eq_sum_range`, the first over `G_i`, the second over
  the lower groups `inertiaLowerGroup T K i` of inertia (`G_i` regarded as a subgroup
  of inertia), up to any bound `b` beyond which the `G_i` vanish. Each is proved with
  only the relevant action installed; the vanishing of `inertiaLowerGroup T K i` for
  `i ≥ b` follows from `Subgroup.bot_subgroupOf`.
- `artinConductor_eq_inertiaArtinConductor_comp`: the Artin expression of a
  representation `ρ` of `G` equals the inertia Artin expression of its restriction
  `ρ.comp (inertia T K).subtype`. With `b` from
  `exists_lowerRamificationGroup_eq_bot`, both sides are the sums above, and they
  agree term by term: `inertiaLowerGroup T K j` has the order of `G_j`
  (`Subgroup.subgroupOfEquivOfLe`, as `G_j` lies in inertia), and its fixed vectors
  under the restriction are those of `G_j` under `ρ`
  (`fixedVectors_comp_subtype_subgroupOf`).
- `artinConductor_rankOne_eq_of_upper_levels`: if a character `χ` of `G` is trivial
  on `G^s` exactly when `a ≤ ⌈s⌉`, for every real `s ≥ 0`, then the Artin expression
  of `rankOneCharacterRepresentation χ` is `a`. By the previous item it is the
  inertia Artin expression of the restriction, which is
  `rankOneCharacterRepresentation (χ.comp (inertia T K).subtype)` (checked pointwise
  by `ext` and `simp`). The published
  `inertiaArtinConductor_rankOne_eq_of_upper_levels` applies, because `G^s` lies in
  inertia for `s ≥ 0`, so triviality of `χ` on `G^s` and triviality of the restricted
  character on the elements of inertia in `G^s` are the same condition.

## Proof of the five clauses

In each clause the proof introduces the target's variables and installs the
target's local instances: the topology `T.topology`, the algebra
`F.Carrier → (L.asPadicField).Carrier` and the scalar tower over `ℚ_[p]`, both
given by `inferInstanceAs` from `L.field` as in the statement.

1. `unitFiltrationComparison` is the published proof.
2. `finiteReciprocityInertiaImages`: the higher unit images at `n = 0`, rewritten
   with `upperRamificationGroup_zero` and `unitFiltration_zero`, give
   `r(T.unitSubgroup) = inertia`. The real unit images at `v = φ(1)`, which is
   nonnegative, give `r(U^(⌈φ(1)⌉)) = G^(φ(1))`; with `⌈φ(1)⌉ = 1` and
   `G^(φ(1)) = G_1` this is `r(U^(1)) = G_1`.
3. `finiteReciprocityConductorTransport`: the upper conductor levels say that `χ` is
   trivial on `G^s` exactly when `a(χ ∘ r) ≤ ⌈s⌉`, for every real `s ≥ 0`. This is
   the hypothesis of `artinConductor_rankOne_eq_of_upper_levels` with
   `a = a(χ ∘ r)`, which gives the Artin expression `a(χ ∘ r)`; the clause is the
   symmetric equality. The rank-one lemma is first specialized to `S` and
   `F.Carrier`, so that its instance arguments are the installed local instances,
   and only then applied to `χ` (as a monoid homomorphism) and the level statement.
4. `finiteReciprocityConductorLevels`: by clause 3, the Artin expression is at most
   `n` exactly when `(a(χ ∘ r) : ℚ) ≤ n`, that is, by `Nat.cast_le`, when
   `a(χ ∘ r) ≤ n`. By `multiplicativeConductor_le_iff_unitFiltration_le_ker` this
   holds exactly when `U^(n)` lies in the kernel of `χ ∘ r`, which is the statement
   that `χ(r(x)) = 1` for every `x ∈ U^(n)`.
5. `finiteReciprocityUnramifiedTameCharacters`: the upper conductor levels at `v = 0`,
   with `⌈0⌉ = 0` and `G^0` = inertia, say `a(χ ∘ r) ≤ 0` exactly when `χ` is trivial
   on inertia, and `a(χ ∘ r) ≤ 0` is `a(χ ∘ r) = 0` (`Nat.le_zero`). At `v = φ(1)`,
   with `⌈φ(1)⌉ = 1` and `G^(φ(1)) = G_1` (used through `SetLike.ext_iff` on
   membership), they say `a(χ ∘ r) ≤ 1` exactly when `χ` is trivial on `G_1`.

The theorem `finiteCharacterConductorTheorems` is the anonymous constructor of these
five proofs.

## Relation to the literature

The target corresponds to Serre, *Local Fields* (1979), XV §2, Theorem 1 and its
corollaries, with VI §2, Propositions 2, 3 and 5. This proof takes the reciprocity
input from the Library's upper-numbering bundle, which proves the analogue of Theorem 1 of
XV §2 in the form `r(U^(⌈v⌉)) = G^v`. The conductor of a character is then computed
from its upper levels by the published rank-one Artin computation on inertia (VI §2,
Proposition 5). The only new mathematical step is the comparison of the Artin
expression of a Galois representation with that of its restriction to inertia, which
holds because both expressions use the same lower groups `G_i ⊆ G_0`.
