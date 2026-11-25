# Proof that general-linear derivatives commute with determinant twists

This module proves the published proposition
`Langlands.Derivative.GeneralLinearDerivativeDeterminantTwistStatement` from
`Langlands.Representation.Derivative.GeneralLinearDerivativeDeterminantTwistStatement`.
The closing theorem is

```lean
theorem Langlands.Derivative.generalLinearDerivativeDeterminantTwist {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    GeneralLinearDerivativeDeterminantTwistStatement.{uF, uV} F T
```

It has universe parameters `uF, uV` in that order. They stay independent, and
the theorem has no hypotheses beyond the statement's outer parameters. Once
`T.topology` is installed, the proof introduces `ψ N k hk s`. It then supplies
the actual natural isomorphism
`DeterminantTwist.generalLinearDerivativeTwistIso T ψ s N k hk`:

`Twist_N(s) ⋙ generalLinearDerivative T ψ N k hk ≅
 generalLinearDerivative T ψ N k hk ⋙ Twist_(N-k)(s)`.

Here `Twist_m(s)` is the published functor `SmoothRep.twistFunctor
(T.determinantPowerCharacter m s) (T.isOpen_ker_determinantPowerCharacter m s)`.
The exponent `s` is the same on both sides. The isomorphism is natural in
arbitrary smooth representations and intertwiners, and it covers every
`k ≤ N`, including `k = 0`, `k = N` and `N = 0`. No finite-length,
admissibility, irreducibility or other premise is used. Lean reports only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## The implemented proof

All helpers are in the namespace `Langlands.Derivative.DeterminantTwist`.
Every natural isomorphism below is an actual `≅` of functors. Composition is in
application order.

### Pasting

`pasteIso` combines two commutation squares `a ⋙ L₁ ≅ L₁ ⋙ b` and
`b ⋙ L₂ ≅ L₂ ⋙ c` into `a ⋙ (L₁ ⋙ L₂) ≅ (L₁ ⋙ L₂) ⋙ c`. It uses associators
and the whiskerings `Functor.isoWhiskerRight e₁ L₂` and
`Functor.isoWhiskerLeft L₁ e₂`. Every derivative functor in the Library is a
composite of restriction, localization, pullback and normalization twists. The
whole proof therefore builds one square per factor and pastes them together.

### Generic squares for an arbitrary group `G`

- `smoothRep_hom_ext`: two smooth intertwiners are equal if their underlying
  maps agree at every vector. This is used to check naturality.
- `twistCongrIso`: twists by equal characters are the same functor, by `subst`
  followed by `Iso.refl`.
- `twistCommIso χ η`: `Tw χ ⋙ Tw η ≅ Tw η ⋙ Tw χ`. Each component is
  `SmoothRep.mkIso (equivOfRepresentationEq _)`. The required equality of
  representations comes from rewriting both sides with the published
  `twist_twist` and using pointwise commutativity `η g * χ g = χ g * η g` in
  `ℂˣ`. Naturality holds componentwise by `rfl`.
- `pullbackTwistIso φ`: `Tw χ ⋙ continuousPullbackFunctor φ ≅
  continuousPullbackFunctor φ ⋙ Tw (χ.comp φ)`. Both sides have the same
  objects and morphisms, so each component is `Iso.refl`.
- `relations_twist`: suppose `U ≤ χ.ker`. Then the published
  `Jacquet.twist_apply_of_le_ker` shows that `twist χ ρ` and `ρ` agree on `U`.
  Hence the `θ`-localization relations
  `Jacquet.Localization.relations (twist χ ρ) U θ` and
  `Jacquet.Localization.relations ρ U θ` are equal. Both are spans of the
  same family `ρ u v - θ(u) • v`.
- `localizationTwistEquiv`: the equality of relations gives
  `Submodule.quotEquivOfEq`. This map is the identity on representatives, and
  it intertwines the localized `M`-action of `twist χ ρ` with the twist by
  `χ.comp M.subtype` of the localized `M`-action of `ρ`. The check on
  generators is `mk (χ m • ρ m v) = χ m • mk (ρ m v)`, which holds because
  `mk` is linear.
- `localizationTwistIso`: when `U ≤ χ.ker`, the published functor
  `Jacquet.Localization.smoothFunctor U θ M` satisfies
  `Tw χ ⋙ Loc ≅ Loc ⋙ Tw (χ.comp M.subtype)`. Its components are the
  previous equivalences. Naturality is checked on quotient representatives
  with `Submodule.Quotient.induction_on`.
- `localizationPullbackTwistIso`: pastes the localization square, the
  pullback square along a continuous `e : H →* M`, and `twistCongrIso` for a
  supplied equality `(χ.comp M.subtype).comp e = η`.

### Determinant-power characters

- `mirabolicPowerCharacter T n s` is
  `(T.determinantPowerCharacter (n + 1) s).comp (mirabolic n F.Carrier).subtype`,
  that is, `|det|^s` restricted to the actual mirabolic subgroup.
  `isOpen_ker_mirabolicPowerCharacter` is the preimage of the published
  open kernel.
- `determinantPowerCharacter_eq_of_determinant_eq`: suppose
  `g ∈ GL_m` and `g' ∈ GL_m'` have the same determinant. Then
  `T.determinantPowerCharacter m s g = T.determinantPowerCharacter m' s g'`,
  because the character is `realPowerCharacter` of
  `T.normalizedAbsUnits ∘ determinant`.
- `determinant_radical`: every element of the actual radical
  `radical n F.Carrier` has determinant one. The published
  `radical_le_upperUnipotent` places it in the upper unipotent subgroup, and
  `Matrix.det_of_isUpperTriangular` together with unit diagonal gives
  determinant one. `radical_le_ker_mirabolicPowerCharacter` then follows from
  the published `T.ker_determinant_le_ker_determinantPowerCharacter`.
- `mirabolicPowerCharacter_levi`: composing the mirabolic character with
  `leviSubgroup n` and `leviContinuousEquiv` gives
  `T.determinantPowerCharacter n s` on `GL_n`.
  `mirabolicPowerCharacter_successor`: composing the rank `n + 1` mirabolic
  character with `successorSubgroup n` and `successorContinuousEquiv` gives the
  rank `n` mirabolic character. Both follow from the previous lemma and the
  published determinant identities `JacquetNormalization.determinant_levi` and
  `JacquetNormalization.determinant_successor`.

### The minus functors, iteration, restriction and rank transport

- `psiMinusUnnormalizedTwistIso` and `phiMinusUnnormalizedTwistIso` instantiate
  `localizationPullbackTwistIso` with the exact data of the published
  `Mirabolic.psiMinusUnnormalized` and `Mirabolic.phiMinusUnnormalized`. For
  `Ψ⁻` the data are the radical, the trivial character, the Levi subgroup and
  `leviContinuousEquiv`. For `Φ⁻` they are the radical, `T.mirabolicTheta ψ n`,
  the successor subgroup and `successorContinuousEquiv`. The hypothesis
  `U ≤ χ.ker` is `radical_le_ker_mirabolicPowerCharacter`, and the character
  equality is the Levi or successor lemma. Each composite is the published
  functor by definition, so the localizing character is unchanged.
- `psiMinusTwistIso` and `phiMinusTwistIso`: the published normalized
  functors are the unnormalized ones followed by the twists by
  `Mirabolic.psiMinusCharacter T n` and `Mirabolic.phiMinusCharacter T n`
  (exponent `-1/2`). Pasting `twistCommIso` swaps `|det|^s` past that
  normalization twist. The exponent `s` is not shifted.
- `phiMinusIterateTwistIso` follows the published recursion of
  `phiMinusIterate`. At `k = 0` the functor is `𝟭`, and the square is
  `rightUnitor ≪≫ leftUnitor.symm`. At `k + 1` it pastes `phiMinusTwistIso` at
  rank `n + k` with the inductive square.
- `mirabolicDerivativeTwistIso` pastes the iterate with `psiMinusTwistIso`.
  This matches `mirabolicDerivative = phiMinusIterate ⋙ psiMinus`.
- `generalLinearRestrictionTwistIso` is `pullbackTwistIso` for the actual
  inclusion `(mirabolic n F.Carrier).subtype`. Here `χ.comp subtype` is
  `mirabolicPowerCharacter T n s` by definition.
- `generalLinearDerivativePositiveTwistIso` pastes restriction at rank `n + k`
  with the mirabolic derivative. This matches
  `generalLinearDerivativePositive = generalLinearRestriction ⋙ mirabolicDerivative`.
- `generalLinearRankCastTwistIso`: for `h : a = b`, `subst h` reduces
  `generalLinearRankCast T h` to the identity functor, and the square becomes
  `rightUnitor ≪≫ leftUnitor.symm`. The twist exponent is carried along the
  transported rank unchanged.
- `generalLinearDerivativeTwistIso` follows the two published cases of
  `generalLinearDerivative`. For `k = 0` the derivative is `𝟭` and
  `N - 0` is `N` by definition. For `k + 1` it is
  `generalLinearRankCast T (rank_eq_of_succ_le hk) ⋙
  generalLinearDerivativePositive T ψ (N - (k + 1)) k`, and the proof pastes the
  rank-cast square with the positive square.

The final theorem wraps this isomorphism in `Nonempty`. No objectwise
comparison, Grothendieck-class equality or support statement replaces the
natural isomorphism.

## Relation to the literature

This is a derived general specialization of Bernstein and Zelevinsky,
*Induced representations of reductive p-adic groups I* (1977). It is registered
as `bernstein-zelevinsky-1977-induced-i`, with retained source SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Proposition 1.9(f), printed p.445 (PDF page 6), states that for a character
`χ` of `G`, `χ ∘ r_{U,θ} = r_{U,χθ} ∘ χ`, and the source says this can be
directly verified. The localization square `localizationTwistIso` is the case
where `χ` is trivial on `U`, so `χθ = θ`. In this case the comparison is an
equality of relation submodules. The minus functors `Ψ⁻ = r_{V,1}` and
`Φ⁻ = r_{V,θ}` and the mirabolic groups are those of §§3.1–3.2, pp.450–451
(PDF pages 11–12). The iterated derivative `Ψ⁻ ∘ (Φ⁻)^(k-1)` is §3.5, p.452
(PDF page 13). The restriction `π^(k) = (π|_P)^(k)` and the order-zero
convention `π^(0) = π` are §4.3, p.454 (PDF page 15). The cited §3.5 is the
BZ77 derivative definition, not the Zelevinsky 1980 §3.5 segment formula. The
Library's normalized minus functors use an explicit `|det|^(-1/2)` twist. The
proof only commutes that fixed twist with `|det|^s`. The Lean route above is
the proof; the citation supplies no step of it.

## Direct imports

- `Langlands.Representation.Derivative.GeneralLinearDerivativeDeterminantTwistStatement`
  (the target statement pair, unchanged)
- `Langlands.Representation.Derivative.MirabolicDeterminant` (published
  determinant identities `determinant_levi` and `determinant_successor`.
  Its only imports are `Langlands.Group.GL.MirabolicRadical`, already in the
  statement's closure, and `Mathlib.LinearAlgebra.Matrix.Block`)

The module imports no Mathlib module directly.

## Transitive project import closure

The recursive traversal of native imports gives 63 project modules: the
statement's 61 audited modules, `Langlands.Representation.Derivative.MirabolicDeterminant`,
and this module. The 56 direct external roots are exactly those recorded in
the statement's Markdown. Every inherited Lean and Markdown pair is
byte-identical to Library commit `35907dc67505e5586fbaafe0233a6a159c266c0d`,
and every module has a nonempty paired Markdown file.

- `Langlands.Group.GL.Basic`
- `Langlands.Group.GL.Blocks`
- `Langlands.Group.GL.Mirabolic`
- `Langlands.Group.GL.MirabolicRadical`
- `Langlands.Group.GL.Nonarchimedean`
- `Langlands.Group.GL.NonarchimedeanStatement`
- `Langlands.Group.GL.NormalizedCharacter`
- `Langlands.Group.GL.Padic`
- `Langlands.Group.GL.RankMaps`
- `Langlands.Group.GL.UpperUnipotent`
- `Langlands.HarmonicAnalysis.Basic`
- `Langlands.LocalField.Canonical`
- `Langlands.LocalField.Definitions`
- `Langlands.LocalField.Normalization.Definitions`
- `Langlands.LocalField.Normalization.Proof`
- `Langlands.LocalField.Normalization.Statement`
- `Langlands.LocalField.Topology`
- `Langlands.Representation.Category.Basic`
- `Langlands.Representation.Category.Twist`
- `Langlands.Representation.Classification.Supercuspidal`
- `Langlands.Representation.Classification.SupercuspidalTwist`
- `Langlands.Representation.Derivative.GeneralLinearDerivativeDeterminantTwistProof` (this module)
- `Langlands.Representation.Derivative.GeneralLinearDerivativeDeterminantTwistStatement`
- `Langlands.Representation.Derivative.Iteration`
- `Langlands.Representation.Derivative.MirabolicCharacter`
- `Langlands.Representation.Derivative.MirabolicDeterminant`
- `Langlands.Representation.Derivative.MirabolicMinus`
- `Langlands.Representation.Dual.Definitions`
- `Langlands.Representation.Jacquet.CharacterTwistEquiv`
- `Langlands.Representation.Jacquet.Coinvariants`
- `Langlands.Representation.Jacquet.Localization`
- `Langlands.Representation.Jacquet.SmoothTwist`
- `Langlands.Representation.MatrixCoefficient.Definitions`
- `Langlands.Representation.MatrixCoefficient.LawsProof`
- `Langlands.Representation.MatrixCoefficient.LawsStatement`
- `Langlands.Representation.Smooth.Admissibility.CofinalProof`
- `Langlands.Representation.Smooth.Admissibility.CofinalStatement`
- `Langlands.Representation.Smooth.Admissibility.EquivalenceProof`
- `Langlands.Representation.Smooth.Admissibility.EquivalenceStatement`
- `Langlands.Representation.Smooth.Definitions`
- `Langlands.Representation.Smooth.FixedVectors.Definitions`
- `Langlands.Representation.Smooth.Transfer.PullbackProof`
- `Langlands.Representation.Smooth.Transfer.PullbackStatement`
- `Langlands.Representation.Smooth.Transfer.SubquotientProof`
- `Langlands.Representation.Smooth.Transfer.SubquotientStatement`
- `Langlands.Representation.Twist.AdmissibilityProof`
- `Langlands.Representation.Twist.AdmissibilityStatement`
- `Langlands.Representation.Twist.AlgebraProof`
- `Langlands.Representation.Twist.AlgebraStatement`
- `Langlands.Representation.Twist.ContinuousCharacterProof`
- `Langlands.Representation.Twist.ContinuousCharacterStatement`
- `Langlands.Representation.Twist.Definitions`
- `Langlands.Representation.Twist.RealPower`
- `Langlands.Representation.Twist.SmoothProof`
- `Langlands.Representation.Twist.SmoothStatement`
- `Langlands.Representation.Twist.SubquotientDefinitions`
- `Langlands.Representation.Twist.SubquotientProof`
- `Langlands.Representation.Twist.SubquotientStatement`
- `Langlands.Representation.Unitary.Basic`
- `Langlands.Representation.Whittaker.Algebraic`
- `Langlands.Representation.Whittaker.GeneralLinear`
- `Langlands.Topology.CompactNormCharacter`
- `Langlands.Topology.Nonarchimedean.Subgroup`

## Mathematical proof dependencies

These are the published declarations the proof uses, grouped by defining
module.

- `Derivative.Iteration`: `phiMinusIterate`, `mirabolicDerivative`,
  `generalLinearRestriction`, `generalLinearDerivativePositive`,
  `generalLinearRankCast`, `rank_eq_of_succ_le`, `generalLinearDerivative`
  (definitions and the rank arithmetic lemma).
- `Derivative.MirabolicMinus`: `Mirabolic.continuousPullbackFunctor`,
  `Mirabolic.psiMinusUnnormalized`, `Mirabolic.phiMinusUnnormalized`,
  `Mirabolic.psiMinus`, `Mirabolic.phiMinus`, `Mirabolic.psiMinusCharacter`,
  `Mirabolic.phiMinusCharacter` and their open-kernel lemmas.
- `Derivative.MirabolicCharacter`: `T.mirabolicTheta`, `Mirabolic.theta_isInvariant`.
- `Derivative.MirabolicDeterminant`: `JacquetNormalization.determinant_levi`,
  `JacquetNormalization.determinant_successor` (matrix determinant identities).
- `Jacquet.Localization`: `relations`, `action`, `IsInvariant`, `isInvariant_one`,
  `mk`, `hom_ext`, `smoothFunctor`.
- `Jacquet.CharacterTwistEquiv`: `Jacquet.twist_apply_of_le_ker` (a twist by a
  character trivial on a subgroup agrees with the original action there).
- `Category.Twist`: `SmoothRep.twistFunctor`, `equivOfRepresentationEq`.
- `Category.Basic`: `SmoothRep.hom`, `SmoothRep.ofHom`, `SmoothRep.mkIso`.
- `Twist.Definitions`, `Twist.AlgebraProof`: `twist`, `twist_twist`.
- `Classification.SupercuspidalTwist`: `T.determinantPowerCharacter`,
  `T.isOpen_ker_determinantPowerCharacter`,
  `T.ker_determinant_le_ker_determinantPowerCharacter` (definitions and
  elementary kernel facts for `|det|^s`. No supercuspidal hypothesis or
  theorem is used).
- `Group.GL.NormalizedCharacter`, `Twist.RealPower`: `T.determinantNorm`,
  `T.normalizedAbsUnits`, `realPowerCharacter`.
- `Group.GL.Basic`, `Group.GL.Mirabolic`, `Group.GL.MirabolicRadical`,
  `Group.GL.UpperUnipotent`: `GeneralLinear.determinant`, `mirabolic`,
  `radical`, `radical_le_upperUnipotent`, `GeneralLinear.upperUnipotent`,
  `leviSubgroup`, `leviContinuousEquiv`, `leviSubgroup_le_normalizer`,
  `successorSubgroup`, `successorContinuousEquiv`,
  `successorSubgroup_le_normalizer`.
- Mathlib: category-theory associators, unitors, whiskering and
  `NatIso.ofComponents`; `Submodule.quotEquivOfEq`,
  `Submodule.Quotient.induction_on`, `Representation.Equiv.mk`,
  `Representation.IntertwiningMap.ext`, `MonoidHom.ext`,
  `Matrix.det_of_isUpperTriangular`, `Finset.prod_eq_one`, `Units.ext`.

No derivative theorem beyond these definitions is used: no exactness, Leibniz
rule, Gelfand–Kazhdan, filtration, highest-derivative or support result.

## Independence audit

The proof may use fully proved general BZ77 derivative and
localization theory, but not the Zelevinsky 1980 segment derivative
formulas 3.5 and 9.6, the results listed under "Proof route" below,
or the segment-socle part of the derivative statements
(`SegmentSocleDerivativesStatement`). This
proof uses less than that. It uses only the published definitions
of restriction, character localization, pullback, the normalized minus
functors and their iteration, together with elementary twist, character and
determinant lemmas. All of these are in the Library at the base commit.

Module contents. The closure is the statement's audited closure plus
`MirabolicDeterminant`, a three-lemma matrix-determinant module extracted from
general derivative normalization. Its only derivative modules are this proof,
the statement, `Iteration`, `MirabolicMinus`, `MirabolicCharacter` and
`MirabolicDeterminant`. Its only Classification modules are `Supercuspidal`
(the definition of supercuspidal representations and classes, with elementary
transport lemmas) and `SupercuspidalTwist` (twist-invariance of
supercuspidality and the determinant-power character). The proof uses only the
character definitions and kernel lemmas from the latter. Its only Whittaker
modules are `Whittaker.Algebraic` and `Whittaker.GeneralLinear`, which define
Whittaker functionals, models and the standard character. The closure
contains no segment, head, socle, multisegment, tempered, square-integrable,
Jacquet-formula, classification-exhaustion, Whittaker-finiteness or
product-irreducibility module.

Name and identifier scan. After comments and strings are removed, no Lean
source in the closure contains `sorry`, `admit`, `axiom`, `native_decide`,
`implemented_by`, `extern`, `#eval` or `run_cmd`. In the same stripped Lean
code, no module contains any of the substrings `Segment`, `segment`, `Socle`, `socle`, `Head`,
`Multisegment`, `multisegment`, `Tempered`, `SquareIntegrable`, `Exhaustion`,
`GenericSegmentProductUniqueness`, `SegmentHeadProductIrreducibility`,
`SquareIntegrableLanglandsClassification`, `SegmentFullJacquetFormula`,
`SegmentHeadJacquetFormula`, `SegmentSocleJacquetFormula` or
`SegmentSpecialJacquetExponentNormFormula`.

Proof route. The proof does not use, in either direction, the conclusions of
these results:

- `GenericSegmentProductUniqueness`,
- multisegment exhaustion,
- ordered strong-head existence,
- quotient coverage,
- ordered conversion,
- tempered uniqueness,
- `SquareIntegrableLanglandsClassification`,
- square-integrable exhaustion,
- regular exhaustion,
- the full `SegmentHeadProductIrreducibility`
  criterion, the consumer of this proof,
- the Ze80 3.5 and 9.6 segment derivative formulas and their proofs,
  and the segment-socle part of the derivative statements
  (`SegmentSocleDerivativesStatement`),
- the segment Jacquet formulas (`SegmentFullJacquetFormula`,
  `SegmentHeadJacquetFormula`, `SegmentSocleJacquetFormula`,
  `SegmentSpecialJacquetExponentNormFormula`),
- socle exhaustion and ordered multisegment socle existence,
- segment-socle irreducibility and socle structure,
- socle commutation and gluing, and downstream swaps,
- analytic segment classification and special-segment square-integrability,
- two-supercuspidal product structure
  and Whittaker coinvariant-finiteness conclusions.

None of these conclusions appears among the proof dependencies listed above,
and none is reachable through the import closure. The support-only segment
theorem and its internal length-two helpers
are not used. This proof supplies no special-head derivative formula, support
comparison or product irreducibility statement.
