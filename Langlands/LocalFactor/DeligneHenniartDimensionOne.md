# Deligne–Henniart Lemma 4.7 for one wild character

This module proves the exact-witness clause and the valuation formula of
`VirtualStabilityStatement` for the line of one wildly ramified character
`χ` of the local Weil group of `F`. That is Deligne–Henniart 1981, Lemma 4.7
(printed pp. 110–111, PDF pp. 22–23), with the valuation of 4.2.2 in
dimension one. The proof is conditional on explicit inputs, listed under the
main theorems:

- the unit-level (upper-numbering) theorem at the bottom field and at the
  relevant larger fields;
- a bundle of Herbrand-function facts for each relevant larger field;
- the inertia comparison and nonempty triviality thresholds.

Throughout, `K` is the bottom field `baseExtension F`. `L` is a finite
intermediate field with `K ≤ L` (`h`). `e_K` and `e_L` are the absolute
ramification indices of `fieldData F K` and `fieldData F L`.

## The norm pullback

- `reciprocityUnits_weilInclusion` (assumes `NormalizedReciprocity`):
  reciprocity at `E` of an element of `W_L` is the norm of its reciprocity at
  `L`. This is the norm relation of the family.
- `restrictCharacter_apply`: the character
  `restrictCharacter F e E L h χ` (module `DeligneHenniartRelativeWitness`) is
  `z ↦ χ (N_{L/E} z)`. DH81 writes it `χ ∘ N_{L/K}`.
- `restrictCharacter_one_add`: suppose `χ(z) = ψ(c (z - 1))` on the principal
  units of level `m` of `E`, and `χ` is trivial on level `A`. Then for `y` of
  positive order in `L` satisfying the two depth conditions of
  `character_norm_one_add`, the value `χ(N(1 + y))` equals
  `(traceCharacter F E L h ψ)(c y)`. This applies the module
  `DeligneHenniartNormTrace` to `E.asPadicField`, `L.asPadicField` and the
  inclusion algebra, and uses `Tr(c y) = c Tr(y)`.

## DH81 4.7 on one larger field

`abelianEpsilonExpression_restrictCharacter_mul` makes the following
assumptions:

- `c ∈ E^×` linearizes `χ` at depth `m`, and `χ` is trivial at level `A`;
- `t` satisfies `(A - 1) e_L < 2 e_E t` and `(m - 1) e_L < e_E t`;
- the conductor `a_L` of the norm pullback satisfies `2 ≤ a_L`,
  `a_L - ⌊a_L/2⌋ ≤ t < a_L`;
- the character `η` of `L` satisfies `a(η) ≤ a_L - t` and `2 a(η) ≤ a_L`.

Then for every Haar measure on `L`,

`abelianEpsilonExpression (restrictCharacter χ · η) ψ_L μ_L =
  η(c⁻¹) · abelianEpsilonExpression (restrictCharacter χ) ψ_L μ_L`,

with `ψ_L = traceCharacter F E L h ψ`. Proof:

1. The published `RankOneStability.exists_deep_linearization` gives a
   linearizer `d` of the pullback on `L` at depth `a_L - ⌊a_L/2⌋`, of order
   `-(n(ψ_L) + a_L)`.
2. On the lattice of order at least `t`, both `c` and `d` give the value of
   the pullback on `1 + y`: `c` by `restrictCharacter_one_add`, and `d`
   because `t ≥ a_L - ⌊a_L/2⌋`.
3. `mul_inv_mem_principalUnits_of_eq_on_lattice` (module `NormTrace`) gives
   `c d⁻¹ ∈ U_L^{a_L - t}`.
4. `abelianEpsilonExpression_mul_of_comparison` then gives the identity. This
   is DH81's "corollaire 1.3(ii)" together with "le corollaire 3.7 nous
   assure l'égalité `η(a) = η(a')`", with the quadratic remainder of 3.3 in
   place of the truncated exponential.

## Depth bookkeeping

`depth_conditions` is integer arithmetic. Let `t = ⌊e_L b / (2 e_K)⌋ + 1`,
`B = ψ(b)` (a natural number) and `ψh = ψ(b/2)`. Its inputs are:

- the slope relation `e_K (B - ψh) = e_L (b/2)`;
- the bound `e_K B ≤ e_L b`;
- `0 < ψh`;
- `a(η) ≤ ⌈ψh⌉`.

From these it derives all the numeric conditions above, with `A = b + 1`,
`m = A - ⌊A/2⌋` and `a_L = B + 1`. DH81's conditions (*) of 4.7 are
`α(L/K) < α(χ)/2` and `α(η) < ψ_{L/K}(α(χ)/2)`. Here they enter through the
slope relation on `[b/2, b]`: the slope of `ψ_{L/K}` beyond `α(L/K)` is the
ramification index, DH81 3.2(iii).

## Conductors on the larger field

- `trivial_iff_of_map_reciprocityUnits`: let a subgroup `H` of `W_E` have
  reciprocity image `U`. Then a field character is trivial on `U` exactly when
  its Weil character is trivial on `H`.
- `restrictCharacter_trivial_iff` makes these assumptions:
  - `χ` on `K` has conductor `b + 1`;
  - the unit-level theorems `hWK` (at `K`, for `baseUpperGroup`) and `hWL`
    (at `L`, for `intermediateUpperGroup` of `DeligneHenniartIntermediateUnits`);
  - a function `ψ` satisfying Herbrand's subgroup formula `hmem` for `L`;
  - the upper group of index `b/2` lies in `W_L`.

  Then for `v ≥ b/2`, the pullback of `χ` is trivial on `U_L^{⌈ψ(v)⌉}`
  exactly when `b < v`. This is DH81 3.3.1 in the case `α(χ) > α(L/K)`.
- `conductor_restrictCharacter`: if moreover `ψ` is continuous, strictly
  increasing and `ψ(0) = 0`, then `ψ(b)` is a natural number `B` and the
  pullback has conductor `B + 1`. This is DH81's `α(χ ∘ N_{L/K}) =
  ψ_{L/K}(α(χ))`. Nontriviality at `v = b` gives the lower bound. Triviality
  at some `v > b` with `ψ(v) < ⌊ψ(b)⌋ + 1`, by continuity, gives the upper
  bound.

## The exact witness at the bottom field

- `HerbrandInput F L b` (definition, a proposition): there is `ψ : ℝ → ℝ`
  with the following properties:
  - it is continuous and strictly increasing, with `ψ 0 = 0`;
  - Herbrand's subgroup formula holds for every `v ≥ 0`: for `w` in the
    standalone Weil group of `L`, the element `intermediateWeilEquiv F L w`
    lies in `upperGroup F v` iff `w` lies in `upperGroup L (ψ v)`;
  - the slope relation `e_K (ψ b - ψ(b/2)) = e_L (b/2)` holds;
  - the bound `e_K ψ b ≤ e_L b` holds.

  Worker 1698's `relativeHerbrandPsi` (Herbrand subextension modules) is
  intended to supply it. It is an explicit hypothesis here.
- `exactWitnessOn_characterClass_of_linearization`: let `χ` on `K` have
  conductor `b + 1` with `b ≥ 1`, and let `c` linearize it at depth
  `b + 1 - ⌊(b+1)/2⌋`. Assume:
  - `IsSystem F e ε`;
  - `AbsoluteUpperInertia F`;
  - the unit-level theorem `hWK` at `K`;
  - for every `L` whose Weil subgroup contains the upper group of index
    `b/2`, the unit-level theorem at `L` and `HerbrandInput F L b`.

  Then `c⁻¹` satisfies `ExactWitnessOn` for `characterClass F e K χ` relative
  to `baseUpperGroup F (b/2)`. Proof: the reduction
  `exactWitnessOn_characterClass` (module `DeligneHenniartRelativeWitness`)
  reduces to the rank-one relation on each such `L`. That relation is the
  previous sections combined:
  - `η` trivial on the upper group gives `a(η) ≤ ⌈ψ(b/2)⌉` through `hWL` and
    Herbrand's formula;
  - `conductor_restrictCharacter` gives `a_L`;
  - `depth_conditions` gives the numerics;
  - `abelianEpsilonExpression_restrictCharacter_mul` gives the identity.

## The target's clauses for a character line

- `exists_linearization`: the published deep linearization in principal-unit
  form. It yields `c` of order `-(a(χ) + n(ψ))` with `χ(z) = ψ(c (z - 1))` on
  `U^{a - ⌊a/2⌋}`.
- `baseFieldCharacter F e χ` (definition): the bottom-field character whose
  Weil character is `χ` restricted along `baseWeilInclusion F`.
- `realizeAtBase_generator_lineBasis`: the bottom realization of the line of
  `χ` (`lineBasis`, module `DeligneHenniartExactCoset`) is
  `characterClass F e K (baseFieldCharacter F e χ)`.
- `isTrivialAt_characterLine_iff`: the line of `χ` is trivial at `r` exactly
  when `χ` is trivial on `upperGroup F r`.
- `breakLabel_lineBasis`: if `baseFieldCharacter F e χ` has conductor `b + 1`,
  then the label of the line is `b`, given `hWK`. Its triviality thresholds
  form the interval `(b, ∞)`.
- `breakSupport_generator`, `minimumBreak_generator` and
  `wildArtinSum_generator_lineBasis` (the last equals `1 + label`) compute
  the target's quantities for a single generator.
- `exists_exactWitness_lineBasis`: for the line `v` of `χ`, with conductor
  `b + 1` and `b ≥ 1`, under `WeilTrivialityThresholdsNonempty` and the
  hypotheses above, there is `γ` (namely `c⁻¹`) with
  - `ord γ = wildArtinSum v + deg v · n(ψ)`, here `(b + 1) + n(ψ)`; this is
    DH81 4.2.2 for `a(χ) = α(χ) + 1`;
  - `ExactWitness F e ε v (minimumBreak F v hv) ψ γ`, via the
    translation `exactWitness_of_exactWitnessOn`.

## Scope

The module does not prove the approximate-witness clause. That clause needs
DH81 3.8/3.12(i) and Corollary 1.3(i). It also treats only characters, not
the induced case of 4.8, and proves none of its hypotheses. In particular
`HerbrandInput`, the unit-level theorems and the inertia comparison remain
hypotheses.

`reciprocityUnits_weilInclusion` is imported from `DeligneHenniartInductionStep`; the shared norm-square theorem retains its exact type.
