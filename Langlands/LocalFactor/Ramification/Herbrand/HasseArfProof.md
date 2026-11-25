# The Hasse–Arf theorem for actual finite p-adic Galois extensions

Lean module: `Langlands.LocalFactor.Ramification.Herbrand.HasseArfProof`
(namespace `Langlands.Ramification.Padic`, as the statement module
`Herbrand/ArithmeticStatement`). It imports `Langlands.LocalFactor.Ramification.Herbrand.QuotientProof`
and the ported Anthropic FLT statement module
`Langlands.LocalFactor.Ramification.HasseArf.Abelian`.

## What the module proves

Let `p` be a prime, `K` and `L` actual `PadicField`s in independent universes with a compatible
algebra `K.Carrier → L.Carrier`, `L/K` Galois, and `T : L.TopologicalData` any realization of
`L`. Write `G = Gal(L/K)`, `G_i = lowerRamificationGroup T K.Carrier i` for the Library's lower
ramification groups (acting on the supplied integer ring `T.Integers`) and
`φ = herbrandPhi T K.Carrier` for the Library's real Herbrand function. The main theorem says:
**if `G` is commutative, then `φ(i)` is an integer at every lower break `i`** (every `i : ℕ` with
`G_i ≠ G_{i+1}`). This is the Library proposition `HasseArfIntegrality K L T` of
`Herbrand/ArithmeticStatement`, a clause of `FiniteHerbrandArithmetic`; it is proved for every `T`,
with no hypothesis added. Its complete type:

```lean
theorem Langlands.Ramification.Padic.hasseArfIntegrality.{uK, uL}
    {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) (L : PadicField.{uL} p)
    [Algebra K.Carrier L.Carrier] [IsScalarTower (Padic p) K.Carrier L.Carrier]
    [IsGalois K.Carrier L.Carrier] (T : L.TopologicalData) :
    HasseArfIntegrality K L T
```

where, unfolded, `HasseArfIntegrality K L T` is

```lean
IsMulCommutative Gal(L.Carrier/K.Carrier) →
  ∀ i : ℕ, lowerRamificationGroup T K.Carrier i ≠ lowerRamificationGroup T K.Carrier (i + 1) →
    ∃ n : ℤ, herbrandPhi T K.Carrier i = n
```

The outer binders are those of the proposition, in its order, so `@hasseArfIntegrality` has
exactly the type `∀ {p} [Fact p.Prime] (K L) [Algebra] [IsScalarTower] [IsGalois] (T),
HasseArfIntegrality K L T` (checked by direct assignment of the unapplied constant, as described in
`notes/lean/complete-declaration-checks.md`). Its level parameters are `uK, uL`.

Two intermediate results are stated for any field `K : Type uK` between `ℚ_p` and an actual
p-adic field `F` (the generic setting of `Herbrand/Finite`), with `T : F.TopologicalData`:

- `lowerGroupOrder_zero_dvd_sum_of_break T K i hi`: if the automorphism group
  `F.Carrier ≃ₐ[K] F.Carrier` is commutative (`IsMulCommutative`), then at a lower break `i`
  the inertia order `lowerGroupOrder T K 0` divides `Σ_{j=1}^{i} lowerGroupOrder T K j`
  (sum over `Finset.Icc 1 i`). This is the ported theorem for the supplied ring and group, in the
  Library's notions.
- `herbrandPhi_natCast_eq_sum_div T K i`: for `i : ℕ`,
  `herbrandPhi T K i = (Σ_{j=1}^{i} lowerGroupOrder T K j : ℕ) / lowerGroupOrder T K 0` in `ℝ`.

## Sources

- Jean-Pierre Serre, *Local Fields*, GTM 67, Springer (1979). Registered as
  `serre-1979-local-fields`, SHA256
  `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`. Used: Chapter IV, §3, the
  Hasse–Arf theorem, printed p. 76 (for an abelian extension the jumps of the upper filtration are
  integers, equivalently `φ(i) ∈ ℤ` at every lower jump `i`), which is the place the Library's
  literature table gives for Hasse–Arf; Serre proves it in Chapter V, §7 (Theorems 1 and 1′,
  printed pp. 93–94). Chapter IV, §1, Proposition 1 (printed p. 62) for the lower numbering, and
  §3 (printed p. 73) for the definition of `φ`.
- The proof is upstream's: the Anthropic Lean formalization of Fermat's Last Theorem
  (`github.com/anthropics/fermats-last-theorem`, commit
  `6e837e75355538c7f80bab5b956861e86c4eacc2`, registered literature
  `anthropic-flt-complete-lean-source-6e837e75`; Apache License 2.0, Copyright 2026 Anthropic,
  PBC; notices in `licenses/Anthropic-FLT/`), file
  `Theorems/Thm_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isMulCommutative.lean`,
  theorem `Langlands.Ramification.hasseArfChain_lowerGroup_of_isMulCommutative`, with
  its import closure of 53 upstream modules. The 30 of them the Library already had and 22 added
  for this proof are in `Langlands/AnthropicFLT/`; the remaining one is upstream's utility module
  `P2M/Util.lean`, whose commands the extract replaces by standard Lean. The pages there describe
  the proof
  (reduction to cyclic quotients through upper numbering; for cyclic groups, the tame character,
  the divisibility of positive breaks by the tame index, Sen's congruences for the wild part and a
  count of the elements of the cyclic wild group by their orders).
- The adapter follows the private experiment of the Library's audit
  `notes/reuse/anthropic-hasse-arf-audit.md` (25 October 2026; its text is in the
  evidence file `anthropic-hasse-arf-evidence/bridge.md`), whose faithful-action argument was
  adapted from the proof in `Ramification/Galois.lean`. That argument is now the public
  `HerbrandBridge.integerAction_faithful` of `Herbrand/QuotientProof`, which is used here, together
  with `HerbrandBridge.sum_Icc_one_eq_sum_range` from the same module.

## Proof (as implemented)

1. **The ring and the group** (`lowerGroupOrder_zero_dvd_sum_of_break`). Install the Library's
   action `integerAction T K` of `G = F.Carrier ≃ₐ[K] F.Carrier` on `T.Integers` and the data
   `T.topology`, `T.valuativeRel`, `T.localField`; then `T.Integers` is a discrete valuation ring with
   finite residue field, and `G` is finite (`F` is finite dimensional over `K`,
   `Module.Finite.of_restrictScalars_finite`).
2. **The hypotheses of the ported theorem.** Faithfulness is
   `HerbrandBridge.integerAction_faithful` (fraction-ring extensionality). The maximal ideal of
   `T.Integers` lies over that of the fixed subring `FixedPoints.subring T.Integers G` by
   `Langlands.Ramification.maximalIdeal_fixedSubring_eq_comap`. With the residue fields written as the quotients by
   the maximal ideals and given explicit `Ideal.Quotient.field` structures, the fixed subring's
   residue field embeds into the finite residue field of `T.Integers` by the lies-over algebra map
   and is finite (`Finite.of_injective`); finite fields are perfect and their algebraic extensions
   separable, so instance search supplies `PerfectField` and `Algebra.IsSeparable`. Commutativity is
   the hypothesis. None of these is a new premise.
3. **The groups.** `Langlands.Ramification.lowerGroup T.Integers G i` is, for the installed action,
   the Library's `lowerRamificationGroup T K i` by definition (both are `lowerGroup T.Integers G i`,
   cf. `HerbrandBridge.lowerRamificationGroup_eq_source`, `rfl`), and both orders are `Nat.card`. So
   the conclusion `Langlands.Ramification.HasseArfChain` of the ported theorem, applied at `i`, is the
   divisibility in the Library's notions; the break hypothesis is the same proposition. There is no
   shift of index conventions: both lower groups are Serre's `G_i`, moving every integer by
   `𝔪^{i+1}`.
4. **The Herbrand function at a natural number** (`herbrandPhi_natCast_eq_sum_div`). The Library's
   floor formula `herbrandPhi_floor` at `u = i` has `⌊i⌋ = i` (`Nat.floor_natCast`), so the
   fractional term vanishes, and `HerbrandBridge.sum_Icc_one_eq_sum_range` turns the sum over
   `range i` of the orders at `j + 1` into the sum over `Icc 1 i`. At `i = 0` both sums are empty.
5. **Integrality** (`hasseArfIntegrality`). At a break `i`, step 1 gives
   `Σ_{j=1}^{i} |G_j| = |G_0| · n`; with `|G_0| > 0` (`lowerGroupOrder_pos`) step 4 gives
   `φ(i) = n`, and the witness is `(n : ℤ)`.

The proof compares only the divisibility of the ported theorem with the Library's own floor formula
for `φ`; it does not compare the source's rational Herbrand function with the Library's real one,
and uses no reciprocity, no Herbrand tower law and no quotient theorem of the Library.

## Declarations, in order

- theorem `Langlands.Ramification.Padic.lowerGroupOrder_zero_dvd_sum_of_break`
- theorem `Langlands.Ramification.Padic.herbrandPhi_natCast_eq_sum_div`
- theorem `Langlands.Ramification.Padic.hasseArfIntegrality`

## Checks

Built with `lake build` on Lean 4.35.0 and Mathlib `56a0058`, without errors or warnings. The three
theorems use only the axioms `propext`, `Classical.choice` and `Quot.sound`. The complete-declaration
check of the main theorem against the telescope of `HasseArfIntegrality` passes.
