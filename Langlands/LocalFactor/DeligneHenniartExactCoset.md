# The exact Deligne–Henniart witness coset

Supporting lemmas for the uniqueness clause of Deligne–Henniart 1981,
Theorem 4.6 (printed p. 110, PDF p. 22): the element `γ` of 4.6.1 is
determined modulo `U(a(V)/2)`. In the Library target
`VirtualStabilityStatement` this is the clause

`∀ γ', ExactWitness F e ε v a ψ γ' ↔ γ' * γ⁻¹ ∈ principalUnits ⌈a / 2⌉₊`

for `a = minimumBreak F v hv`. The published helper
`exactWitness_coset` (in `DeligneHenniartWitnessGroups`) already reduces
this clause to witnesses with zero input `v = 0`. This module identifies the
zero-input witnesses with the principal units of level `⌈a / 2⌉₊` of the
bottom field `(baseExtension F).field`.

The lemmas use unproved published propositions. Each one is an explicit
hypothesis, named as follows:

- `hthr : WeilTrivialityThresholdsNonempty.{uF, max uF uV} F`: every
  continuous finite-dimensional representation of the local Weil group has a
  nonempty set of triviality thresholds. Only the inclusion `⊇` uses it.
- `hreal : AbsoluteReciprocityRealUnitImages.{uF}`,
  `hinert : AbsoluteUpperInertia F F.canonicalTopologicalData`,
  `hcmp : UnitFiltrationComparison.{uF}`, and
  `he : GeometricWeilReciprocityRelation F F.canonicalTopologicalData
  (Correspondence.baseReciprocityCandidate F eC)`. These are exactly the
  inputs of the published helper `baseUpperGroup_map_reciprocityUnits`
  (module `DeligneHenniartUpperUnits`): for `s ≥ 0`, the base component of
  `eC` maps `baseUpperGroup F s` onto the bottom field's principal units of
  level `⌈s⌉₊`.
- In the last corollary, `he` is replaced by
  `hgeo : CommonClosureGeometricStatement.{uF, uF}`, through the published
  `geometric_baseReciprocityCandidate`.

## Determinants of low-break virtual representations

- `determinantCharacter_generator_eq_one` (assumes `hthr`): if
  `breakLabel F b < t` and `g ∈ upperGroup F t`, then the exact determinant of
  `LocalWeil.realizeExact F (generator b)` takes the value `1` at `g`.
  Proof: let `A` be a representative of the class `b`. Its label is the real
  infimum of its triviality thresholds. That set is nonempty by `hthr`, so it
  contains some `r < t`. Then `A` is trivial on `upperGroup F r`, so also on
  `upperGroup F t` (`isTrivialAt_mono`). Hence `A(g)` is the identity, and its
  determinant is `1`.
- `determinantCharacter_realizeExact_eq_one` (assumes `hthr`): the same holds
  for every lattice element `w` with `AllBreaksBelow F w t`. Proof: induction
  over finitely supported functions, using additivity of the determinant and
  its behaviour on integer multiples.
- `determinantCharacter_realizeAtBase`: for `g` in the bottom Weil subgroup,
  the determinant of `realizeAtBase F w` at `g` equals the determinant of
  `LocalWeil.realizeExact F w` at `g`, viewed in the local Weil group. The
  base realization is a restriction, and the determinant commutes with
  restriction.
- `determinantCharacter_realizeAtBase_eq_one` (assumes `hthr`): combines the
  two previous lemmas for `g ∈ baseUpperGroup F t`.
- `fieldDeterminant_eq_one_of_mem_principalUnits` (assumes `hthr`, `hreal`,
  `hinert`, `hcmp`, `he`): let `t ≥ 0` and `AllBreaksBelow F w t`. Then the
  descended field character `fieldDeterminant F eC _ (realizeAtBase F w)` is
  trivial on the principal units of level `⌈t⌉₊`. Proof: such a unit equals
  `reciprocityUnits F eC _ g` for some `g ∈ baseUpperGroup F t`, by
  `baseUpperGroup_map_reciprocityUnits`. Then `fieldDeterminant_reciprocityUnits`
  and the previous lemma give the value `1`. Equivalently, by
  `multiplicativeTrivialAt_iff_conductor_le`, this field character has
  multiplicative conductor at most `⌈t⌉₊`. This corresponds to the remark at
  the start of the proof of DH81 Lemma 4.7, which bounds the last
  ramification break: `β(W) < a/2` implies `α(det W) < a/2`. The bound in
  DH81 is on the break `α`, not on the conductor exponent. For a ramified
  character the conductor exponent is `α + 1` (DH81 0.5–0.7 and 1.2). The
  lemma here proves only triviality on `U^⌈t⌉`.

## Rank-one test representations

- `mem_baseWeil`: every local Weil element lies in the bottom Weil subgroup.
  This follows from `baseWeil_eq_top`.
- `baseWeilSection` (definition): the continuous homomorphism from the local
  Weil group to the bottom Weil subgroup `weilSubgroup F (baseExtension F)`
  sending `w` to `⟨w, mem_baseWeil F w⟩`. It is the inverse of
  `baseWeilInclusion F`. `baseWeilSection_val` and `coe_baseWeilSection`
  record that the two maps are mutually inverse, by `rfl`.
- `baseWeilCharacter` (definition): for a common-closure family `eC` and a
  bottom-field character `η`, the continuous character of the local Weil
  group given by `weilCharacter F eC (baseExtension F) η` composed with
  `baseWeilSection F`. `baseWeilCharacter_apply`: on a bottom Weil element
  `g` it takes the value `η (reciprocityUnits F eC _ g)`.
- `lineBasis` (definition): for a continuous character `χ` of the local Weil
  group, the irreducible rank-one class of its character line
  `FiniteRepresentation.characterLine χ`, formed with `LocalWeil.basisClass`.
  - `realizeExact_generator_lineBasis`: its generator realizes to
    `ExactGrothendieckGroup.characterClass χ`.
  - `degree_generator_lineBasis`: it has degree `1`.
  - `determinantCharacter_generator_lineBasis`: its determinant is `χ`.
  - `breakLabel_lineBasis_le`: let `r ≥ 0` and let `χ` be trivial on
    `upperGroup F r`. Then the label of `lineBasis χ` is at most `r`, because
    `r` is a triviality threshold of the line.
- `lineDifference` (definition): the degree-zero test
  `generator (lineBasis χ) - generator (lineBasis 1)`, that is, `[χ] - [1]`.
  - `degree_lineDifference`: it has degree `0`.
  - `determinantCharacter_lineDifference`: its exact determinant is `χ`.
  - `allBreaksBelow_lineDifference`: let `0 ≤ r < b` and let `χ` be trivial
    on `upperGroup F r`. Then every class with nonzero coefficient in
    `lineDifference χ` has label `< b`. Such a class is one of the two lines,
    and their labels are at most `r` and at most `0`, respectively.

## The zero-input annihilator

- `mem_principalUnits_of_fieldDeterminant_eq_one` (assumes `hreal`,
  `hinert`, `hcmp`, `he`, and `0 < a`; no `hthr`): suppose that
  `fieldDeterminant F eC _ (realizeAtBase F w) δ = 1` for every degree-zero
  `w` with `AllBreaksBelow F w (a / 2)`. Then `δ` lies in the principal units
  of level `m = ⌈a / 2⌉₊`. This is the uniqueness argument of DH81 4.6: it
  suffices to test `W = η - 1` with `η` trivial on `U(a(V)/2)`.
  Proof: by the published criterion
  `PadicAbelian.mem_principalUnits_iff_bounded_characters`, it suffices to
  show `η δ = 1` for every bottom-field character `η` of conductor at most
  `m`. Since `a > 0`, we have `m ≥ 1` and `m - 1 < a / 2`. Put
  `r = ((m - 1) + a / 2) / 2`, so `0 ≤ r`, `m - 1 < r < a / 2`, and
  `m ≤ ⌈r⌉₊`. By `baseUpperGroup_map_reciprocityUnits` at `r`, the
  reciprocity image of each `baseWeilSection F w` with
  `w ∈ upperGroup F r` lies in the principal units of level `⌈r⌉₊`, hence of
  level `m`. There `η` is trivial, by
  `multiplicativeTrivialAt_iff_conductor_le`. So
  `χ = baseWeilCharacter F eC η` is trivial on `upperGroup F r`. The test
  `lineDifference χ` has degree `0` and all labels below `a / 2`. Write `δ`
  as a reciprocity image of some `g`, using `reciprocityUnits_surjective`.
  Then the hypothesis for this test, together with
  `fieldDeterminant_reciprocityUnits`, `determinantCharacter_realizeAtBase`,
  `determinantCharacter_lineDifference` and `baseWeilCharacter_apply`, gives
  `η δ = 1`.
- `exactWitness_zero_iff` (assumes `hthr`, `hreal`, `hinert`, `hcmp`, `he`,
  `AdditiveRelation F ε`, and `0 < a`): `ExactWitness F eC ε 0 a ψ δ` holds
  if and only if `δ` lies in the principal units of level `⌈a / 2⌉₊`.
  Proof: rewrite with the published `exactWitness_iff`. For zero input, the
  tensor product is `0`, and the assignment takes the value `1` on `0`
  (`value_zero`). So the witness condition says that every admissible field
  determinant takes the value `1` at `δ`, for every Haar measure.
  - `⊆`: Haar measures on the bottom field exist (private lemma
    `haarMeasure_nonempty`, built from `normalizedAdditiveHaar` on a positive
    compact set). Then apply the previous lemma.
  - `⊇`: apply `fieldDeterminant_eq_one_of_mem_principalUnits` with
    `t = a / 2`.
- `exactWitness_iff_mem_coset` (same hypotheses): if `γ` is an exact witness
  for `(v, a, ψ)`, then `γ'` is one if and only if `γ' * γ⁻¹` lies in the
  principal units of level `⌈a / 2⌉₊`. Proof: compose the published
  `exactWitness_coset` with `exactWitness_zero_iff`.
- `exactWitness_iff_mem_coset_of_isSystem` (assumes `hthr`, `hreal`,
  `hinert`, `hcmp`, `hgeo`): the same statement for `IsSystem F eC ε`, a
  lattice element `v` with nonempty break support `hv` and
  `PositiveBreakSupport F v`, and `a = minimumBreak F v hv`. This is the
  coset clause of `VirtualStabilityStatement`, relative to any exact witness
  `γ`. Proof: the normalization and additivity conjuncts of `IsSystem` give
  `he` (via `geometric_baseReciprocityCandidate`) and `AdditiveRelation`.
  Positivity of the minimum break comes from
  `positiveBreakSupport_iff_minimumBreak_pos`.

## Scope

The module proves neither the existence of an exact witness nor the
valuation formula nor the approximate-witness clauses of the target, and it
does not prove any of the hypotheses listed above. Index conventions: DH81
0.1 defines `U(t) = {u : v(u - 1) ≥ t}` for real `t`, which is the
principal-unit group of level `⌈t⌉`. DH81 0.4 fixes the upper ramification
convention, which the published filtration `upperGroup` follows.
