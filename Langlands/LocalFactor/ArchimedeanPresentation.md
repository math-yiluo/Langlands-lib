# Arithmetic factors of finite archimedean Weil presentations

This module builds callable L- and epsilon-factor attachments for finite
direct sums of the published archimedean character blocks. It also builds
the real-induction blocks. The blocks are the published
`ComplexCharacterData` and `RealCharacterData` of
`Langlands.LocalFactor.ArchimedeanAttachment`. The block epsilons are the
published scaled constructors of `Langlands.LocalFactor.ArchimedeanScaling`.
Every factor is a finite product of these published block factors. Every
presentation has an actual continuous sum representation, built from the
published `FiniteRepresentation.sum`.

A supplied continuous representation gets factors only through supplied
presentation data. That data is a block list together with an actual
invertible linear intertwiner from the block list's sum model to the
representation. The module chooses no presentation and proves no
independence of the presentation.

All declarations are in the namespace `Langlands.LocalFactor.Archimedean`.

## Sum models

- `zeroRepresentation G` is the trivial representation of `G` on
  `Fin 0 -> Complex`, as a continuous object. It is the empty sum. Its
  action is constant, so it is continuous for the module topology.
  `zeroRepresentation_rank` proves its rank is `0`.
- `continuousSum A B` is the published binary sum
  `FiniteRepresentation.sum A.val B.val` of two continuous representations.
  It is packaged with the published continuity theorem
  `Langlands.Weil.OperationClosure.continuous_prod`. `continuousSum_val` exposes the
  underlying sum, and `continuousSum_rank` proves additivity of rank using
  Mathlib's `Module.finrank_prod`.
- `complexModel ds`, for `ds : List ComplexCharacterData`, is defined by
  recursion on the list. The empty list goes to `zeroRepresentation ComplexWeil`,
  and `d :: ds` goes to `continuousSum d.representation (complexModel ds)`.
  `complexModel_val` proves that the underlying representation is the fold
  `foldr (fun d A => sum (complexCharacter d.character).val A) (trivial on Fin 0 -> Complex)`.
  `complexModel_rank` proves rank `ds.length`, since each block has rank one.
- `RealBlock` is an inductive type with two constructors.
  `RealBlock.character d` holds a `RealCharacterData`.
  `RealBlock.induced d` holds a `ComplexCharacterData`, used through its
  actual two-dimensional real induction `realInducedRepresentation`.
  `RealBlock.equivSum` identifies `RealBlock` with
  `RealCharacterData ⊕ ComplexCharacterData`. Induced blocks of weight zero
  are allowed. Their irreducibility is not asserted (it fails: Tate (2.2.2.1)).
- `realModel xs` is built the same way from `RealBlock.representation`.
  `realModel_val` gives the corresponding fold. `RealBlock.representation_character`
  and `RealBlock.representation_induced` identify the blocks with
  `realCharacter d.character` and `realInducedCharacter d.character`.
  `realRank xs` is the sum of the block ranks `RealBlock.rank`: one for a
  character, two for an induction. `realModel_rank` proves that the model has
  rank `realRank xs`.

The models are `FiniteRepresentation.ContinuousObjects.{0, 0}` objects of the
published groups `ComplexWeil` and `RealWeil`. No new representation type or
category is introduced.

## Complex presentation factors

For `ds : List ComplexCharacterData`:

| Declaration | Definition |
| --- | --- |
| `complexLFactor ds` | `ReciprocalEntire.product (ds.map ComplexCharacterData.lFactor)` |
| `complexStandardEpsilon ds` | product in `Complex units` of the published `standardEpsilon` |
| `complexEpsilon ds a c hc s` | product in `Complex units` of `d.epsilon a c hc s` |

In `complexEpsilon`, `a : Complex units` selects the published
`complexScaledCharacter a`. `c : NNReal` with `hc : 0 < c` selects
`complexScaledMeasure c hc`. `s : Complex` is the spectral parameter of the
published block convention, the twist by `‖.‖^(2*s)`.

Proved laws:

- Products: `complexLFactor_nil` (the published `ReciprocalEntire.one`),
  `complexLFactor_cons`, `complexLFactor_singleton`, `complexLFactor_append`,
  `complexLFactor_perm` and `denominator_complexLFactor`. The epsilon analogues
  are `complexStandardEpsilon_nil`, `complexStandardEpsilon_cons`,
  `complexEpsilon_nil`, `complexEpsilon_cons`, `complexEpsilon_singleton`,
  `complexEpsilon_append` and `complexEpsilon_perm`.
- Gamma form: `complexLFactor_eq_shiftProduct` writes the factor as the
  product of `gammaComplex.shift (t + |m|/2)` over the blocks. Here `t` is a
  block's exponent and `m` its weight. `complexLFactor_eq_gammaProduct`
  identifies the factor with the published `gammaProduct` of the blocks
  `ComplexCharacterData.gammaBlock d = GammaBlock.complex (t + |m|/2)`.
- Poles: `complexLFactor_isPole` proves that `s` is a pole exactly when
  `s + (t + |m|/2) = -n` for some block and some natural `n`.
  `complexLFactor_regular_iff` gives the complementary description of the
  regular domain `denominator s ≠ 0`.
- Evaluation only on the regular domain: `complexBlockRegularPoint` turns a
  regular point of the product into a regular point of each listed block.
  `coe_eval_complexLFactor` proves that `eval` at a regular point is the
  product of the block evaluations, indexed by `List.attach`. No numerical
  value is given at a pole.
- Closed epsilon formula, `coe_complexEpsilon`, where `n = ds.length`:
  `c^n * prod chi_d(a) * ‖a‖^(2*n*(s-1)) * prod i^|m_d|`.
  `coe_complexStandardEpsilon` gives `prod i^|m_d|`.
- Nonvanishing (`complexEpsilon_ne_zero`) holds because the value is a unit.
  Entire dependence on `s` (`differentiable_complexEpsilon`) is proved by
  induction from the block lemmas.
- Standard normalization: `complexEpsilon_standard` gives
  `complexEpsilon ds 1 1 _ s = complexStandardEpsilon ds` for every `s`.
- Haar scaling: `complexEpsilon_measure_scale` proves that replacing `c` by
  `b*c`, with `0 < b`, multiplies the value by `b^rank`. Here `rank` is the
  rank of the actual model `(complexModel ds).val`.

## Real presentation factors

Block-level wrappers in the namespace `RealBlock`:

| Declaration | `character d` | `induced d` |
| --- | --- | --- |
| `lFactor` | `d.lFactor = gammaReal.shift (t + e)` | `d.realInducedLFactor = gammaComplex.shift (t + |m|/2)` |
| `gammaBlock` | `GammaBlock.real (t + e)` | `GammaBlock.complex (t + |m|/2)` |
| `standardEpsilon` | `i^e` | `i^(|m|+1)` |
| `determinant a` | `chi(a)` | `sign(a) * chi(realToComplex a)` |
| `epsilon a c hc s` | `d.epsilon a c hc s` | `d.realInducedEpsilon a c hc s` |
| `rank` | `1` | `2` |

Here `e` is the parity of a real datum, and `t`, `m` are the exponent and
weight. The `induced` column keeps three features of real induction: the
extra phase `i`, the sign-times-restricted-character determinant multiplier,
and the rank-two measure exponent. The published `ArchimedeanAttachment`
and `ArchimedeanScaling` Markdown explain these features. `RealBlock.coe_epsilon` gives
`c^rank * determinant(a) * |a|^(rank*(s-1)) * standardEpsilon` uniformly.
`RealBlock.epsilon_measure_scale`, `RealBlock.differentiable_epsilon` and
`RealBlock.epsilon_standard` restate the published block laws. The lemmas
`lFactor_character`, `lFactor_induced`, `lFactor_isPole_character`,
`lFactor_isPole_induced`, `coe_standardEpsilon_character`,
`coe_standardEpsilon_induced`, `coe_determinant_character` and
`coe_determinant_induced` expose the table entries.

For `xs : List RealBlock`, `realLFactor`, `realStandardEpsilon` and
`realEpsilon` are the products of the block factors. They have the same
laws as in the complex case: `nil`, `cons`, `singleton`, `append`, `perm`,
`denominator_realLFactor`, `realLFactor_eq_gammaProduct`,
`realLFactor_isPole`, `realLFactor_regular_iff`, `realBlockRegularPoint`,
`coe_eval_realLFactor`, `realEpsilon_ne_zero`, `differentiable_realEpsilon`,
`realEpsilon_standard` and `realEpsilon_measure_scale`.

`realLFactor_isPole` reports two kinds of pole. A real character block has
poles at `s + (t + e) = -2n`. An induced block has poles at
`s + (t + |m|/2) = -n`. The closed formula `coe_realEpsilon` reads
`c^r * prod determinant_x(a) * |a|^(r*(s-1)) * prod standardEpsilon_x`,
where `r = realRank xs`. Haar scaling multiplies by `b` to the rank of the
actual model `(realModel xs).val`.

## Attachment to a supplied representation

`ComplexPresentation V` and `RealPresentation V` are structures. Each has a
field `blocks`, a block list, and a field `intertwiner`, a
`FiniteRepresentation.Equiv` from the block list's model to `V.val`. Here `V`
is a continuous representation of the relevant Weil group whose carrier lies
in an arbitrary universe `uV`. The published cross-universe `Equiv` is a
linear isomorphism of the carriers that commutes with the group actions.

For a presentation `P`, `P.lFactor`, `P.standardEpsilon` and
`P.epsilon a c hc s` are the factors of `P.blocks`. They depend on `P`
explicitly. Proved facts:

- `rank_eq`: `V.val.rank` equals `P.blocks.length` in the complex case and
  `realRank P.blocks` in the real case. The proof transports the model rank
  along the intertwiner by the published `FiniteRepresentation.rank_eq_of_equiv`.
- `lFactor_isPole`, `epsilon_ne_zero`, `differentiable_epsilon` and
  `epsilon_standard` restate the list laws for `P`.
- `epsilon_measure_scale`: replacing `c` by `b*c` multiplies the attached
  epsilon by `b^(V.val.rank)`. This is the rank of the supplied target.
- `ofModel ds` presents `complexModel ds` by the identity intertwiner, and
  `RealPresentation.ofModel` does the same for real block lists.
  `transport P e` moves a presentation of `V` to `W` along an actual
  equivalence `e`, keeping the blocks (`transport_blocks`).

## Connection with `ArchimedeanPresentationStatement`

The published propositions `ComplexFactorPresentationIndependenceStatement`
and `RealFactorPresentationIndependenceStatement` use let-bound raw formulas
on lists of parameter triples. This module does not import those
propositions and does not use them as hypotheses. It neither edits nor
restates them. The correspondence is as follows.

- Complex case: send `d` to `(d.character, (d.weight, d.exponent))`. The
  statement's `compatible` condition is the field `d.character_eq`. Under
  this map the statement's `model`, `lFactor`, `standardEpsilon` and
  `epsilon` correspond, respectively, to `complexModel_val`,
  `complexLFactor_eq_shiftProduct`, `coe_complexStandardEpsilon` and
  `coe_complexEpsilon`.
- Real case: `RealBlock.equivSum` matches the statement's sum type. Send a
  real datum to `(character, (parity, exponent))` and a complex datum to
  `(character, (weight, exponent))`. The statement's block clauses then
  correspond to `RealBlock.representation_character` and
  `RealBlock.representation_induced` (`blockModel`), to `lFactor_character`
  and `lFactor_induced` (`blockFactor`), and to the
  `coe_standardEpsilon_*` lemmas (`blockEpsilon`). They also correspond to
  `RealBlock.rank` (`blockRank`) and the `coe_determinant_*` lemmas
  (`blockDeterminant`). The published `realToComplex` has the same
  definition as the statement's local one. Finally `realModel_val`,
  `realLFactor`, `realRank` and `coe_realEpsilon` match the statement's
  `model`, `lFactor`, `rank` and `epsilon`.

Under this correspondence, the first conjunct of each statement is proved
here for these lists: nonvanishing and entire dependence of epsilon. The
second conjunct is presentation independence. Two presentations `P` and `Q` of the
same `V` give an actual equivalence of models,
`P.intertwiner.trans Q.intertwiner.symm`. So the published proposition,
once proved, would give equal attached factors. This module neither states
nor proves that implication.

## Design choices

- `RealBlock` is an inductive type rather than a bare sum type, so that the
  block names are readable. `RealBlock.equivSum` records that the two are
  equivalent.
- The models are defined by structural recursion, so `cons` laws hold by
  definition. The fold form needed for comparison with the statement is a
  theorem. The empty list gives an actual rank-zero continuous
  representation.
- L-factors stay `ReciprocalEntire` objects with their pole data. They are
  never replaced by a total complex function. Numerical evaluation exists
  only at `RegularPoint`s.
- Epsilon factors are products in `Complex units`. This gives nonvanishing
  directly and makes the empty product `1`.
- Haar scaling is stated with the exponent equal to the rank of the actual
  model, or of the supplied target. It is not just a count of blocks.

## Original source and provenance

John Tate, *Number theoretic background*, Corvallis Part II (1979),
literature ID `tate-1979-number-theoretic-background`. Retained original:
`/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`,
SHA-256 `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
The PDF page number is the printed page number plus 9. The cited pages were
read directly for this module. No source-specific erratum note exists in the
current notes roots.

- (2.2.2), printed p.10/PDF19: the quasi-characters of archimedean
  `W_F` are the only irreducibles for `F = C`. For `F = R` the remaining
  irreducibles are inductions `Ind(z^(-N) omega_s)` with `N > 0`.
  (2.2.2.1) says the induction is reducible for `N = 0`, which is why
  irreducibility of weight-zero induced blocks is not asserted.
- (3.1.1) and the complex L definition, pp.12--13/PDF21--22: the Gamma
  factors of characters. The complex definition carries the printed label
  "(3.2.1)" at the top of p.13; by its position it is (3.1.2).
- (3.2.2)--(3.2.5), p.13/PDF22: Haar scaling by `r`, character scaling
  by `chi(a)||a||^(-1)`, and the standard plus characters, measures and
  phases.
- (3.3.1), p.14/PDF23: L is additive, so it is defined on irreducibles,
  and `L(Ind chi) = L(chi)` for real induction.
- (3.4.1)--(3.4.5) and (3.4.8), pp.14--15/PDF23--24: (3.4.1) is the
  existence theorem, which is the boundary of this module. (3.4.2) gives
  additivity, (3.4.3) Haar scaling by `r^(dim V)`, and (3.4.4) character
  scaling by `det V(a) ||a||^(-dim V)`. (3.4.5) treats spectral twisting and
  (3.4.8) induction in degree zero.

Tate states no formula for finite presentations. The products here are
defined directly. They agree with what additivity, (3.3.1) and (3.4.2),
requires of a direct sum of blocks. Each block factor is the published
construction, whose derivation from Tate's formulas (including the induction
phase `i`) is documented with that construction. Tate's existence and
uniqueness theorem (3.4.1) is not used or assumed.

## Scope and exclusions

The following remain separate statement or proof obligations:

- classification of finite continuous representations;
- existence of a presentation for a given representation;
- independence of the factors from the presentation, or descent to
  isomorphism classes;
- analytic functional equations;
- global comparison;
- identification with a nonabelian local-constant system.

No reciprocity identification, self-dual-measure theorem or epsilon system
is assumed.

## Dependencies

The module imports `Langlands.LocalFactor.ArchimedeanScaling`,
`Langlands.Weil.Representation.SumsTensor` and
`Langlands.Weil.Representation.OperationClosureProof`, with their published
dependencies. Environment: Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
