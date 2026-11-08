# Deligne–Henniart Lemma 4.7 over an intermediate field

The module `DeligneHenniartDimensionOne` proves Deligne–Henniart 1981,
Lemma 4.7 (printed pp. 110–111, PDF pp. 22–23), for a character of the bottom
field `K = baseExtension F`, with tests relative to the upper group of `F`.
This module proves the same lemma for a character of an arbitrary finite
intermediate field `E` of the common closure. Here the tests are relative to
the upper ramification groups of `E` itself.

DH81 4.8 (printed p. 111, PDF p. 23) needs this form. It applies 4.7 to
characters `χ_i` of the fields `L_i` of a Brauer decomposition, with the
upper numbering of `L_i`.

Throughout, `E ≤ L` are finite intermediate fields (`h : E.field ≤ L.field`).
`e_E` and `e_L` are the absolute ramification indices of `fieldData F E` and
`fieldData F L`. The upper groups of `E` are `intermediateUpperGroup F E s`
(module `DeligneHenniartIntermediateUnits`). This is the image in
`W_E = weilSubgroup F E` of the upper group
`upperGroup (E.asPadicField) s` of the standalone Weil group of `E`, under
`intermediateWeilEquiv F E`.

## The carried upper groups

- `intermediateUpperGroup_antitone`: `s ↦ intermediateUpperGroup F E s` is
  antitone. This comes from antitonicity of `upperGroup`.
- `intermediateUpperGroup_normal`: each such group is normal in `W_E`. It is
  the image of a normal subgroup under a surjective map.
- `intermediateUpperGroup_le_inertia`: assume `AbsoluteUpperInertia` for
  `E.asPadicField` and its canonical data. Then for `s ≥ 0` the group lies in
  the inertia subgroup `CommonClosureWeilDeligne.inertia F E`. Proof: by
  antitonicity the preimage lies in `upperGroup (E.asPadicField) 0`. That
  group is the local inertia of `E.asPadicField`, by the inertia hypothesis
  and the published `localInertia_eq_comap`. The published
  `intermediateWeilMap_mem_localInertia` then carries it into the inertia of
  `F`.

## Conductors on the larger field

The hypotheses common to the next two lemmas:

- `χ`, a character of `E^×`, has conductor `b + 1`;
- `hWE` and `hWL` are the unit-level (upper-numbering) theorems at `E` and at
  `L`: for `s ≥ 0`, `reciprocityUnits F e E` maps
  `intermediateUpperGroup F E s` onto the principal units of level `⌈s⌉₊`, and
  likewise for `L`;
- `ψH : ℝ → ℝ` satisfies the relative Herbrand subgroup formula `hmem`: for
  `v ≥ 0` and `g ∈ W_L`, the element `weilInclusion F E L h g` lies in
  `intermediateUpperGroup F E v` exactly when `g` lies in
  `intermediateUpperGroup F L (ψH v)`;
- `hNL`: every element of `intermediateUpperGroup F E (b/2)` lies in `W_L`.

The lemmas:

- `restrictCharacter_trivial_iff_rel`: for `v ≥ b/2` with `ψH v ≥ 0`, the norm
  pullback `restrictCharacter F e E L h χ` is trivial on the principal units of
  `L` of level `⌈ψH v⌉₊` exactly when `b < v`. This is DH81 3.3.1 in the case
  `α(χ) > α(L/E)`. The proof is that of `restrictCharacter_trivial_iff` in
  `DeligneHenniartDimensionOne`, with `hmem` in place of the comparison
  through the upper groups of `F`.
- `conductor_restrictCharacter_rel`: assume moreover that `ψH` is continuous
  and strictly increasing with `ψH 0 = 0`. Then `ψH b` is a natural number `B`,
  and the pullback has conductor `B + 1`. This is DH81's
  `α(χ ∘ N_{L/E}) = ψ_{L/E}(α(χ))`. The proof is that of
  `conductor_restrictCharacter`.

## The exact witness over `E`

- `HerbrandInputRel F E L h b` (definition, a proposition): there is
  `ψH : ℝ → ℝ` with the following properties:
  - it is continuous and strictly increasing, with `ψH 0 = 0`;
  - it satisfies the relative subgroup formula `hmem` above for every `v ≥ 0`;
  - the slope relation `e_E (ψH b - ψH (b/2)) = e_L (b/2)` holds;
  - the bound `e_E ψH b ≤ e_L b` holds.

  These are the properties of Herbrand's function `ψ_{L/E}` used by DH81 4.7:
  Herbrand's theorem (Serre, *Local Fields*, IV §3, Proposition 15 and
  Remark 2), and DH81 3.2(iii) on the slopes. By 3.2(iii) the slope of
  `ψ_{L/E}` is `e_L/e_E` beyond `α(L/E)` and at most `e_L/e_E` everywhere.
  The definition is a hypothesis bundle. This module proves none of it.
- `exactWitnessOn_characterClass_of_linearization_rel`: let `χ` on `E` have
  conductor `b + 1` with `b ≥ 1`. Let `c ∈ E^×` linearize it at depth
  `b + 1 - ⌊(b+1)/2⌋`: `χ(z) = ψ(c (z - 1))` on those principal units.
  Assume:
  - `IsSystem F e ε`;
  - `AbsoluteUpperInertia` for `E.asPadicField`;
  - the unit-level theorem `hWE` at `E`;
  - for every `L ⊇ E` such that `W_L` contains
    `intermediateUpperGroup F E (b/2)`: the unit-level theorem at `L` and
    `HerbrandInputRel F E L h b`.

  Then `c⁻¹` satisfies `ExactWitnessOn` for `characterClass F e E χ` relative
  to `intermediateUpperGroup F E (b/2)`. The proof is that of
  `exactWitnessOn_characterClass_of_linearization`:
  1. The relative-witness reduction `exactWitnessOn_characterClass` reduces
     to the rank-one relation on each such `L`. Its hypotheses `hN` and `hNI`
     are the two lemmas of the first section.
  2. A test character `η` of `W_L` trivial on the upper group has conductor at
     most `⌈ψH (b/2)⌉`, by `hWL` and the subgroup formula.
  3. `conductor_restrictCharacter_rel` gives the conductor `B + 1` of the
     pullback.
  4. `depth_conditions` (with `e_E` in place of `e_K`) gives the numerical
     conditions.
  5. `abelianEpsilonExpression_restrictCharacter_mul` gives the identity.
- `exists_exactWitnessOn_rel` packages the theorem with the published deep
  linearization (`exists_linearization`). Under the same hypotheses, there
  is `γ ∈ E^×` (namely `c⁻¹`) such that:
  - `ord_E γ = (b + 1) + n(ψ)`, where `n(ψ)` is
    `(fieldData F E).additiveConductor ψ`; this is the dimension-one case of
    DH81 4.2.2 over `E`;
  - `γ` is an exact witness for `characterClass F e E χ` relative to
    `intermediateUpperGroup F E (b/2)`.

## Scope

The module proves none of its hypotheses: the unit-level theorems, the
inertia comparison or `HerbrandInputRel`. It does not perform the induction
step of DH81 4.8. Worker 1698's module `DeligneHenniartUpperComparison`
treats that step. Its upper groups `weilUpperSubgroup F L s` are the
preimages of the same standalone upper groups under the inverse of the same
equivalence, so they equal `intermediateUpperGroup F L s`. This module states
no lemma comparing the two. It also does not treat the approximate-witness
clause.
