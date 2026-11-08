# Deligne–Henniart witnesses relative to a normal subgroup

Supporting definitions and lemmas for the existence part of
`VirtualStabilityStatement` (Deligne–Henniart 1981, Theorems 4.2 and 4.6).
The module does three things:

- It defines witness relations over any finite intermediate field `E` of the
  common closure. Their tests are the degree-zero classes spanned by
  representations trivial on a subgroup `N` of `W_E`.
- It carries out the representation-theoretic half of DH81 4.4 and 4.7 for a
  character class. What remains is a rank-one twist relation on larger fields.
- It translates the relative relations at the bottom field into the target's
  `ExactWitness` and `ApproximateWitness`.

## Additivity

- `fieldDeterminant_add_apply`, `fieldDeterminant_zero_apply`,
  `fieldDeterminant_zsmul_apply`: the published descended determinant
  `fieldDeterminant F e E x`, evaluated at a fixed `γ`, is additive in `x`.
  Proof: write `γ` as a reciprocity image (`reciprocityUnits_surjective`), then
  use `fieldDeterminant_reciprocityUnits` and the additivity of the exact
  determinant.
- `value_zsmul`, `value_sub`: an assignment satisfying `AdditiveRelation`
  sends `n • x` to the `n`th power and `x - y` to the quotient. They come from
  the published `valueAddHom` and `value_neg`.
- `exists_haarMeasure`: every finite intermediate field carries an additive
  Haar measure, namely `normalizedAdditiveHaar` on a positive compact set.

## Relative witness relations

- `ExactWitnessOn F e ε E N ψ x γ` (definition): for every
  `w ∈ weilTrivialOnSpan F E N` of degree zero and every Haar measure `μ` on
  `E`, `ε E ψ μ (continuousTensorSame w x) = fieldDeterminant F e E w γ`. The
  span `weilTrivialOnSpan F E N` is the published integral span of the classes
  of continuous representations of `W_E` on which `N` acts trivially. This is
  DH81's test condition "the constituents of `W` are trivial on `N`", for
  example `N = W(t/2)` in 4.6 (printed p. 110, PDF p. 22).
- `ApproximateWitnessOn F e ε E N ψ x γ` (definition): the same tests. For
  each test and each `μ` there is `n` with both sides equal after raising to
  the power `p ^ n`. This is the relation "mod* `Q_p/Z_p(1)`" of DH81 4.2.1.
- `exactWitnessOn_of_span`: if every degree-zero element of
  `weilTrivialOnSpan F E N` lies in the integral span of a set `S`, it
  suffices to check the exact relation on `S`. Proof: induction over the span,
  using additivity of both sides in the test.
- `approximateWitnessOn_of_span`: the same for the approximate relation. The
  ratio of the two sides, written additively in `Additive ℂˣ` (private
  `ratioHom`), is additive in the test. The published `pPowerTorsion` subgroup
  (module `DeligneHenniartWitnessGroups`) is closed under sums and integer
  multiples.

## Induced rank-one tests against a character class

- `restrictCharacter F e E L h χ` (definition): for a field character `χ` of
  `E` and `E ≤ L`, the field character of `L` corresponding, under the
  published `fieldCharacterEquiv`, to the restriction of `weilCharacter F e E χ`
  along `weilInclusion F E L h`. DH81 writes this character as `χ ∘ N_{L/K}`
  (4.4). This module does not prove that identification with the norm.
  `weilCharacter_restrictCharacter` records the defining property.
- `weilCharacter_mul` and `weilCharacter_apply`: `weilCharacter` is
  multiplicative and is evaluation at the reciprocity image.
- `continuousTensorSame_induce_characterClass`: the tensor product of
  `Ind_{W_L}^{W_E} ([η] - [1])` with `[χ]` is
  `Ind_{W_L}^{W_E} ([χ|·η] - [χ|])`. This uses the published
  `continuousTensor_characterClass` (tensor with a line is a twist),
  `continuousTwist_induce` (projection formula for twists) and
  `continuousTwist_characterClass`.
- `value_induce_characterClass` (assumes `IsSystem F e ε`): the epsilon value
  of that test is
  `ε_L([restrictCharacter χ · η']) · ε_L([restrictCharacter χ])⁻¹`, computed
  with the trace character `traceCharacter F E L h ψ` and any Haar measure on
  `L`. Here `η'` is the field character of `η`. Proof: the induction law of
  `IsSystem` in degree zero, then `value_sub`.
- `fieldDeterminant_induce_characterClass` (assumes `NormalizedReciprocity`):
  the determinant of `Ind_{W_L}^{W_E} ([η] - [1])` at `γ` is `η'(γ)`, with `γ`
  viewed in `L` through `unitsInclusion`. Proof: the published
  `determinant_induce_degreeZero_reciprocity`, which combines Gallagher's
  theorem with the transfer/inclusion square of normalized reciprocity. The
  public `gallagherDeterminant` discharges Gallagher's theorem. This is DH81's
  `det W = η|_{K^*}` in 4.4 (printed p. 110, PDF p. 22).
- `exactWitnessOn_characterClass` (assumes `IsSystem F e ε`, `N` normal and
  `N ≤ CommonClosureWeilDeligne.inertia F E`): `γ` satisfies
  `ExactWitnessOn F e ε E N ψ (characterClass F e E χ) γ` provided the
  following rank-one relation holds. For every `L ⊇ E` with `N ≤ W_L`, every
  continuous character `η` of `W_L` trivial on `N`, and every Haar measure
  `μ_L` on `L`,

  `abelianEpsilonExpression (restrictCharacter χ · η') ψ_L μ_L =
    η'(γ) · abelianEpsilonExpression (restrictCharacter χ) ψ_L μ_L`,

  with `ψ_L = traceCharacter F E L h ψ`. Proof: the public
  `weilRelativeDegreeZeroBrauer` (DH81's use of the variant [1] 1.5 of
  Brauer's theorem in dimension zero, printed p. 109, PDF p. 21) writes every
  test as an integral combination of the classes `Ind_{W_L} ([η] - [1])`. The
  previous lemmas and the rank-one law of `IsSystem` evaluate both sides on
  each class. This is the reduction "de la même manière qu'en 4.4" in DH81
  4.7 (printed pp. 110–111, PDF pp. 22–23).
- `approximateWitnessOn_characterClass` (same assumptions): the same
  conclusion for `ApproximateWitnessOn`, when the rank-one relation holds
  after raising both sides to some power `p ^ k`. This is the reduction of
  DH81 4.4.

## Translation at the bottom field

- `upperGroup_normal` and `baseUpperGroup_normal`: the upper groups are
  normal, as preimages of the normal absolute upper groups.
- `baseUpperGroup_le_inertia` (assumes
  `hinert : AbsoluteUpperInertia F F.canonicalTopologicalData`): for `r ≥ 0`,
  `baseUpperGroup F r` lies in `CommonClosureWeilDeligne.inertia F
  (baseExtension F)`. Proof: `upperGroup F r ≤ upperGroup F 0`, and `hinert`
  with the published `localInertia_eq_comap` identifies `upperGroup F 0` with
  the degree-zero subgroup.
- `realizeAtBase_generator_mem` (assumes
  `hthr : WeilTrivialityThresholdsNonempty.{uF, max uF uV} F`): if
  `breakLabel F b < r`, then `realizeAtBase F (generator b)` lies in
  `weilTrivialOnSpan F (baseExtension F) (baseUpperGroup F r)`. Proof: a
  representative `A` of `b` has a triviality threshold below `r` (nonempty
  thresholds and the definition of the label as their infimum), so it is
  trivial on `upperGroup F r`. The base realization of the generator is the
  class of the restriction of `A` (`realizeExact_ofRepresentation`,
  `restrict_ofRepresentation`).
- `realizeAtBase_mem_weilTrivialOnSpan` (assumes `hthr`): the same for every
  lattice element `w` with `AllBreaksBelow F w r`, by induction over finitely
  supported functions.
- `realizeAtBase_mem_degreeZero`: degree zero is preserved
  (`degree_realizeAtBase`).
- `exactWitness_of_exactWitnessOn` (assumes `hthr`): the relation
  `ExactWitnessOn F e ε (baseExtension F) (baseUpperGroup F (a / 2)) ψ
  (realizeAtBase F v) γ` implies the target's `ExactWitness F e ε v a ψ γ`.
  Proof: rewrite with the published `exactWitness_iff`. Every target test is
  a relative test by the two previous lemmas.
- `approximateWitness_of_approximateWitnessOn` (assumes `hthr`): the same with
  `baseUpperGroup F a` and the approximate relations
  (`approximateWitness_iff`).

## Scope

The module does not prove the rank-one twist relations on the larger fields
`L`. Those need the ramification of `restrictCharacter χ` and of `η`
(Herbrand functions), the norm–trace comparison of DH81 chapter 3, and the
rank-one twist formulas of DH81 1.1–1.3. It also does not treat induced
inputs `x = Ind χ` (DH81 4.5 and 4.8), the valuation formula, or the
target theorem. The only unproved published propositions used are the
explicit hypotheses `hthr` and `hinert` of the last section.
