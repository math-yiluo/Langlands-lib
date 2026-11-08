# The approximate witness for one wild character

This module proves the approximate-witness clause of
`VirtualStabilityStatement` for one wildly ramified character. That is
Deligne–Henniart 1981, Lemma 4.3 with its proof 4.4 (printed p. 109,
PDF p. 21). Together with the exact clause of `DeligneHenniartDimensionOne`
and the two coset theorems, it gives every clause of the target for the line
of one character, in `virtualStability_lineBasis`. The proof is conditional
on explicit inputs, listed with each theorem. The main one is the first-order
norm–trace congruence of DH81 3.12(i) on each relevant larger field.

Throughout, `E ≤ L` are finite intermediate fields of the common closure
(`h : E.field ≤ L.field`). `χ` is a character of `E^×` of conductor `b + 1`,
`b ≥ 1`. Its norm pullback to `L` is `restrictCharacter F e E L h χ`. The
additive character of `L` is `traceCharacter F E L h ψ`. `U^n` denotes
`principalUnits n` of the relevant `fieldData`.

## Inputs

- `TopLayerInput F E L h b B` (definition, a proposition): for every nonzero
  `y ∈ L` with `B ≤ ord_L y`:
  - `Tr_{L/E} y` has order at least `b`;
  - for all units `z = 1 + y` of `L` and `t = 1 + Tr y` of `E`,
    `N_{L/E}(z) t⁻¹ ∈ U_E^{b+1}`.

  For `B = ψ_{L/E}(b)` and `b > α(L/E)`, this is DH81 3.12(i), the statement
  `TopLayerNormTraceStatement` of the helper module
  `DeligneHenniartTopLayerStatement`, applied to `L ⊆ M` for a Galois closure
  `M`. This module does not make that deduction.
- `ApproximateHerbrandInput F E L h U b` (definition, a proposition). Here
  `U : ℝ → Subgroup (weilSubgroup F E)` is a family of subgroups. It asserts
  that there is `ψH : ℝ → ℝ` with:
  - `ψH` continuous and strictly increasing, with `ψH 0 = 0`;
  - Herbrand's subgroup formula: for `v ≥ 0` and `g ∈ W_L`,
    `weilInclusion F E L h g ∈ U v` iff
    `g ∈ intermediateUpperGroup F L (ψH v)`;
  - `TopLayerInput F E L h b (ψH b)`.

  Unlike the exact case, no slope condition is needed.

## Conductors for a family of subgroups

These generalize `restrictCharacter_trivial_iff_rel` and
`conductor_restrictCharacter_rel` of `DeligneHenniartDimensionOneRelative`.
There, the family is `intermediateUpperGroup F E` and the threshold is `b/2`.
Here both are arbitrary.

`restrictCharacter_trivial_iff_family` makes these assumptions:

- an antitone family `U` with the unit-level theorem `hWE`: for `s ≥ 0`,
  `reciprocityUnits F e E` maps `U s` onto `U_E^{⌈s⌉₊}`;
- the unit-level theorem `hWL` at `L`;
- Herbrand's formula `hmem`;
- a threshold `s₀ ≥ 0` with `U s₀` inside `W_L`.

Then for `v ≥ s₀`, the pullback is trivial on `U_L^{⌈ψH v⌉₊}` exactly when
`b < v`. `conductor_restrictCharacter_family` then shows the following, for
`s₀ ≤ b` and `ψH` continuous and strictly increasing with `ψH 0 = 0`: `ψH b`
is a natural number `B`, and the pullback has conductor `B + 1`.

## The comparison of linearizers (DH81 4.4)

`mul_inv_mem_principalUnits_one_of_topLayer` makes these assumptions:

- `NormalizedReciprocity F e`;
- `c ∈ E^×` linearizes `χ` at depth `b + 1 - ⌊(b+1)/2⌋`;
- the pullback has conductor `B + 1` with `B ≥ 1`;
- `TopLayerInput F E L h b B`;
- `d ∈ L^×`, of order `-(n(ψ_L) + B + 1)`, linearizes the pullback at depth
  `(B + 1) - ⌊(B+1)/2⌋` (as produced by the published
  `RankOneStability.exists_deep_linearization`).

Then `c d⁻¹ ∈ U_L^1`, where `c` is viewed in `L`. Proof: take `x ∈ L` of
order at least `B`, and set `t = 1 + Tr x`, a principal unit of level `b`.
Then:

- `ψ_L(d x) = χ(N(1 + x))`, by the linearization of the pullback
  (`restrictCharacter_apply`: the pullback is `χ ∘ N`);
- `χ(N(1 + x)) = χ(t)`, because `N(1 + x) t⁻¹ ∈ U_E^{b+1}` and `χ` has
  conductor `b + 1`;
- `χ(t) = ψ(c Tr x)`, by the linearization of `χ`;
- `ψ(c Tr x) = ψ_L(c x)`, by the definition of the trace character.

So `c` and `d` define the same character on the lattice of order at least
`B`. Then `mul_inv_mem_principalUnits_of_eq_on_lattice` (module
`DeligneHenniartNormTrace`) with `t = B` and `A = B + 1` gives level one. In
DH81 this is the step "`χ ∘ N_{L/K}(Ey) = χ(E(Tr y)) = ψ(a Tr y)` for `y` of
valuation `ψ_{L/K}(α(χ))`".

## The approximate witness

`approximateWitnessOn_characterClass_of_linearization_family` makes these
assumptions:

- `IsSystem F e ε`;
- a family `U` that is antitone and normal, with `U s` in the inertia
  subgroup of `W_E` for `s ≥ 0`;
- `c` as above;
- the unit-level theorem for `U`;
- for every `L` whose Weil subgroup contains `U b`: the unit-level theorem
  at `L` and `ApproximateHerbrandInput F E L h U b`.

Then `c⁻¹` satisfies `ApproximateWitnessOn` for `characterClass F e E χ`
relative to `U b`. Proof:

1. The relative-witness reduction `approximateWitnessOn_characterClass`
   (module `DeligneHenniartRelativeWitness`) reduces to the rank-one relation
   up to `p`-power roots of unity on each such `L`.
2. A test character trivial on `U b` has conductor at most `B = ψH b`, by
   `hWL` and Herbrand's formula. This is less than `B + 1`, the conductor of
   the pullback.
3. The comparison above gives `c d⁻¹ ∈ U_L^1`.
4. `approximateTwistWitness_of_comparison` (module
   `DeligneHenniartApproximateRankOne`, DH81 1.3(i)) gives the relation at
   `c⁻¹`.

Two specializations follow:

- `approximateWitnessOn_characterClass_of_linearization`: the bottom field
  with `U = baseUpperGroup F`. This family is antitone by
  `baseUpperGroup_antitone`. Here `AbsoluteUpperInertia F` is assumed.
- `approximateWitnessOn_characterClass_of_linearization_rel`: an
  intermediate field `E` with `U = intermediateUpperGroup F E`. Here
  `AbsoluteUpperInertia` for `E.asPadicField` is assumed. This is the form
  needed by the induction step DH81 4.5.

## Every clause for the line of one character

`virtualStability_lineBasis` concerns the line `v` of a character `χ` of the
local Weil group whose bottom-field character `baseFieldCharacter F e χ` has
conductor `b + 1 ≥ 2`. It assumes:

- `WeilTrivialityThresholdsNonempty`, `AbsoluteReciprocityRealUnitImages`,
  `AbsoluteUpperInertia F`, `UnitFiltrationComparison`,
  `CommonClosureGeometricStatement` and `IsSystem F e ε`;
- `hLexact`: the hypotheses of the exact case
  (`exactWitnessOn_characterClass_of_linearization`), i.e. the unit-level
  theorem and `HerbrandInput F L b` for every `L` whose Weil subgroup
  contains the upper group of index `b/2`;
- `hLapprox`: the unit-level theorem and
  `ApproximateHerbrandInput F K L h (baseUpperGroup F) b` for every `L` whose
  Weil subgroup contains `baseUpperGroup F b`.

The conclusion is the body of `VirtualStabilityStatement` for `v`, for every
proof `hv` of nonempty break support and every `PositiveBreakSupport`. There
is `γ` with:

- `ord γ = wildArtinSum v + deg v · n(ψ)`;
- `γ` is an exact witness at the minimum break, and the exact witnesses are
  exactly the coset `γ U^{⌈a/2⌉₊}`;
- `γ₀ = γ` is an approximate witness with `γ γ₀⁻¹ = 1 ∈ U^1`, and the
  approximate witnesses are exactly the coset `γ₀ U^1`.

Proof: let `c` be a linearizer (`exists_linearization`). The bottom-field
unit-level theorem follows from `baseUpperGroup_map_reciprocityUnits` and
`geometric_baseReciprocityCandidate`. Then:

- the valuation and the exact clause are as in `exists_exactWitness_lineBasis`;
- the approximate clause for `c⁻¹` is the bottom-field specialization above,
  translated by `approximateWitness_of_approximateWitnessOn`;
- the two cosets are `exactWitness_iff_mem_coset_of_isSystem` and
  `approximateWitness_iff_mem_coset_of_isSystem`.

This is DH81 4.6 for `V` of dimension one, including "cet élément `γ` est
congru à celui de (4.2.1) mod* `U(1)`". Here the two elements are equal.

## Scope

The module proves none of its hypotheses. In particular it does not derive
`TopLayerInput` from `TopLayerNormTraceStatement`, does not prove the
Herbrand inputs, and does not treat representations of dimension greater
than one (DH81 4.5 and 4.8).
