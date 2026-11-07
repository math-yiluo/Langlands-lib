# Whittaker completeness: finitely many exceptional twists

This supporting module provides the counting step (P6) of the proof of Whittaker
completeness (`Langlands.Whittaker.WhittakerCompletenessStatement`, Jacquet and
Shalika 1985, `jacquet-shalika-1985-ramified-factors`, Lemma (3.2), printed page
325). It does not prove that statement by itself.

The proof of the statement is by induction on the number of linked pairs among the
supercuspidal blocks `τ_1, …, τ_k` of a normalized product. The unlinked base case is
the published module `Langlands.Representation.Whittaker.CompletenessUnlinkedBase`.
In the inductive step a linked pair crossing a cut is separated by twisting the
blocks on one side of the cut by `ν^u`. This module shows that this lowers the
number of linked pairs for every `u ≠ 0` close to `0`. The deformation itself and
the passage to the limit `u → 0` are written separately.

## Conventions

`ν = |det|` is the character `T.determinantPowerCharacter n 1`. A cuspidal datum
`PadicField.TopologicalData.CuspidalDatum.{uV, uF} T` is Zelevinsky's element of
`𝒞`: a rank `r > 0` together with an isomorphism class of
irreducible supercuspidal representations of `GL_r(F)`. `ρ.twist s` is the class of
`ρ ⊗ ν^s` for real `s`. The datum `ρ_a` of a family `ρ : Fin k → CuspidalDatum T` is
linked to `ρ_b` when `ρ_a = ν ρ_b`, that is `ρ a = (ρ b).twist 1`. This is the
ordered relation of Bernstein and Zelevinsky 1977, §4.2, Theorem: by that theorem
and the published P4a, a product with no such pair is irreducible. In the section on
blocks the canonical topology, valuation and local-field structures of `F` are
local instances, as in `CompletenessUnlinkedBase`.

## Declarations

### Real twists of a cuspidal datum

In the namespace `Langlands.PadicField.TopologicalData.CuspidalDatum`:

- `twist_eq_self_iff ρ s`: `ρ.twist s = ρ ↔ s = 0` for every real `s`. The Library
  proves this for integer `s` (`Classification.cuspidalIntegralTwistFreeness`). Its
  helper `Classification.IntegralTwistFreeness.exponent_eq_zero_of_equiv` already
  works for real exponents: an equivalence `ρ ⊗ ν^s ≅ ρ` forces `s = 0`, because
  `ν^s` takes the value `q^(-r s)` on the scalar uniformizer while the central
  character cancels. The proof here repeats the Library's passage from equality of
  classes to an equivalence (`SupercuspidalRep.isoClass_eq_iff`,
  `SmoothRep.equivOfIso`) and applies that helper.
- `twist_injective ρ`, `twist_inj`: `s ↦ ρ.twist s` is injective. This follows
  from `twist_eq_self_iff` and `twist_twist`.
- `twist_left_inj s`: `ρ.twist s = σ.twist s ↔ ρ = σ`.
- `ne_twist_one ρ`: `ρ ≠ ρ.twist 1`, so no datum is linked to itself.

### Linked pairs

In the namespace `Langlands.Whittaker`, for `ρ : Fin k → CuspidalDatum T`:

- `linkedPairs ρ` is the set of ordered pairs `(a, b)` with `ρ a = (ρ b).twist 1`
  (`mem_linkedPairs`), and `linkedCount ρ` is its cardinality (`Set.ncard`).
- `linkedCount_eq_zero_iff ρ`: `linkedCount ρ = 0` iff `ρ a ≠ (ρ b).twist 1` for all
  `a, b`. The right side is the hypothesis `hunl` of the published P4a for
  `ρ = blockDatum τ hs hirr hsc`.
- `exists_crossing_of_linkedCount_ne_zero ρ h`: if `linkedCount ρ ≠ 0`, there are
  `j, a, b` with `¬(j < a ↔ j < b)` and `ρ a = (ρ b).twist 1`. A linked pair has
  `a ≠ b` by `ne_twist_one`, and the cut after `min a b` separates it.

### Twisting one side of a cut

Let `S : Fin k → Prop` be decidable; the cut after `j` is `S = (j < ·)`.

- `twistOn S u ρ a = (ρ a).twist (if S a then u else 0)`: twist the data with `S a`
  by `ν^u` and leave the others unchanged. `twistOn_of_pos`, `twistOn_of_neg` and
  `twistOn_zero` (`twistOn S 0 ρ = ρ`) unfold it.
- `twistOn_linked_iff_of_iff`: if `S a ↔ S b`, the pair `(a, b)` is linked in
  `twistOn S u ρ` iff it is linked in `ρ`. Both data receive the same twist, which
  cancels by `twist_left_inj`.
- `subsingleton_setOf_crossing_linked S ρ a b`: the set of `u` for which
  `¬(S a ↔ S b)` and `(a, b)` is linked in `twistOn S u ρ` has at most one element.
  If `S a` and not `S b`, the condition is `(ρ a).twist u = (ρ b).twist 1`; if `S b`
  and not `S a`, it is `ρ a = (ρ b).twist (u + 1)`. In both cases `twist_inj` gives
  at most one `u`.
- `finite_setOf_crossing_linked S ρ` (P6): the set of `u` for which some crossing
  pair (`¬(S a ↔ S b)`) is linked in `twistOn S u ρ` is finite. It is a finite union
  of the previous sets.
- `eventually_not_crossing_linked S ρ`: for all `u` in a punctured neighbourhood of
  `0` (`∀ᶠ u in 𝓝[≠] 0`), no crossing pair is linked in `twistOn S u ρ`. A finite
  set minus `{0}` is closed and misses `0`.
- `linkedPairs_twistOn_subset S ρ hu`: if no crossing pair is linked in
  `twistOn S u ρ` (`hu`), then `linkedPairs (twistOn S u ρ) ⊆ linkedPairs ρ`.
- `linkedCount_twistOn_lt S ρ hu h`: if moreover some crossing pair is linked in `ρ`
  (`h`), the inclusion is strict and
  `linkedCount (twistOn S u ρ) < linkedCount ρ`.
- `eventually_linkedCount_twistOn_lt S ρ h` (P6, counting form): if some crossing
  pair is linked in `ρ`, then `linkedCount (twistOn S u ρ) < linkedCount ρ` for all
  `u` in a punctured neighbourhood of `0`.

### Twisting blocks

For blocks `τ i` of `GL_(m i + 1)(F)` with carriers `W i` and `c : Fin k → ℝ`:

- `twistBlocks c τ a = twist (determinantPowerCharacter (m a + 1) (c a)) (τ a)` is
  the block `τ a ⊗ |det|^(c a)` for the canonical structures.
- `isSmooth_twistBlocks`, `isIrreducible_twistBlocks`,
  `isSupercuspidal_twistBlocks`: twisting keeps the blocks smooth, irreducible and
  supercuspidal (published `isSmooth_twist_iff`, `isIrreducible_twist_iff`,
  `GeneralLinear.isSupercuspidal_twist_iff`).
- `blockDatum_twistBlocks`: for any proofs of these properties,
  `blockDatum (twistBlocks c τ) … a = (blockDatum τ … a).twist (c a)`. This holds by
  `rfl`, as for the published `supercuspidalDatum_twist`.
- `blockDatum_twistBlocks_ite S u`: with `c i = if S i then u else 0`,
  `blockDatum (twistBlocks c τ) … = twistOn S u (blockDatum τ …)`, again by `rfl`.
  So the counting lemmas above apply to the data of the deformed blocks.

## Provenance

The module is derived. `twist_eq_self_iff` extends the Library's
`Classification.cuspidalIntegralTwistFreeness` from integer to real exponents with
the same central-character argument, which the Library helper
`IntegralTwistFreeness.exponent_eq_zero_of_equiv` already proves for real `s`. The
linkage relation is that of Bernstein and Zelevinsky 1977, §4.2, Theorem. The other
declarations are internal helpers for the proof of Jacquet and Shalika 1985, Lemma
(3.2): finite combinatorics of linked pairs and the published twist-stability lemmas
for smooth, irreducible and supercuspidal representations. Worker 1810, who writes the
induction, assigned this step to Worker 228. Worker 228
wrote the module.
