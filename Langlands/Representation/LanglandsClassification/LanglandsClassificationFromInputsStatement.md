# The Langlands classification from its remaining inputs

Author: Worker 5295. Module
`Langlands.Representation.LanglandsClassification.LanglandsClassificationFromInputsStatement`,
namespace `Langlands.Aubert.General.RepresentedParabolic`.

The module contains one `Prop`-valued definition,
`LanglandsClassificationFromInputsStatement.{u, v}`. It is neither assumed nor proved
here.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, VII.4.2, Theorem (printed p.243 / PDF p.249) and its proof (to printed p.246 /
PDF p.252). The registered source ID is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The conclusion is the
published `LanglandsClassificationStatement`. See `LanglandsClassificationStatement.md`.

## The statement

`LanglandsClassificationFromInputsStatement.{u, v}` is an iterated implication. Its
conclusion is `LanglandsClassificationStatement.{u, v}`, the conjunction of parts (i), (ii)
and (iii) of VII.4.2 for fields `k : Type u` and smooth representations of `M(F)` with
carriers in `Type v`. Part (i) says that `i_P^G(σ ⊗ ψ)` has a unique irreducible quotient.
Part (ii) says that two Langlands triplets with a common irreducible quotient have the same
standard Levi, unramified characters of the same absolute value, and isomorphic twists.
Part (iii) says that every irreducible smooth representation of `G(F)` on a carrier in
`Type v` is a quotient of `i_P^G(σ ⊗ ψ)` for some Langlands triplet. Its premises are four
published propositions, in this order:

1. `LeviSecondAdjointnessStatement.{u, v}` (Renard VI.9.6, first Theorem, (VI.9.6.1)). Take
   any nonarchimedean local field `k : Type u`, any connected reductive `G` and any two
   actual rational parabolic triples `P = MN` (`p`, `m`, `n`) and `P̄ = M N̄` (`pbar`, `mbar`,
   `nbar`) with `mbar ≫ pbar = m ≫ p` and `pointImage p ⊓ pointImage pbar = pointImage (m ≫ p)`.
   Then normalized induction `leviInductionFunctor.{u, max u v} p m n …` is left adjoint to
   the normalized Jacquet functor `leviJacquetFunctor.{u, max u v} pbar mbar nbar …`, on
   smooth representations with carriers in `Type (max u v)`.
2. `LeviInductionFiniteLengthStatement.{u, v}` (Renard VI.6.2). For every actual rational
   parabolic `P = MN` of a connected reductive `G` over such a `k`,
   `leviInductionFunctor.{u, v}` satisfies `SmoothRep.PreservesFiniteLength`: it sends smooth
   representations of `M(F)` of finite length to smooth representations of `G(F)` of finite
   length.
3. `RationalPointsIrreducibleAdmissibleStatement.{u, v}` (Jacquet's theorem, Renard VI.2.2,
   Theorem). For every nonarchimedean local field `F : Type u` and every connected reductive
   `G`, every irreducible `A : SmoothRep.{0, u, v} ℂ (RationalPoint F G.X)` is admissible. The
   topology on the rational points is `rationalPointTopology F G.X`.
4. `LeviJacquetFiniteLengthStatement.{u, v}` (Renard VI.6.4). For every actual rational
   parabolic `P = MN` of such a `G`, the normalized Jacquet functor
   `leviJacquetFunctor.{u, v}` satisfies `SmoothRep.PreservesFiniteLength`.

## Why these premises

Renard's proof of VII.4.2 uses the VII.4.1 Lemma, second adjointness (VI.9.6), Frobenius
reciprocity, Langlands' combinatorial lemma V.3.18, the geometric lemma, and the finiteness
properties of Chapter VI. In the represented-parabolic interface of the Library, every
other input of this proof is a published theorem or, in one case, an accepted proof awaiting
publication:

- the VII.4.1 Lemma, as `langlandsTripletOppositeKernel` (module `LanglandsTripletRegularityProof`);
- the identity support of the opposite intertwining space, as `oppositeIdentitySupport`;
- the mutual rigidity used in part (ii), as `langlandsTripletMutualOppositeIntertwiningRigidity`,
  with its corollary `langlandsQuotientInjective_of_secondAdjointness`;
- V.3.18, as `Langlands.GroupScheme.langlandsCombinatorialDecomposition`;
- restriction of exponents to larger standard Levi subgroups, as
  `oppositeStandardExponentRestriction`;
- the temperedness criterion for unitary untwists (`OppositeUntwistTemperedCriterionStatement`),
  proved by Worker 63's `oppositeUntwistTemperedCriterion`, a proof candidate of Task 5295
  (4c051806) that has passed review but is not yet published.

The proof of this statement will be staged only after that candidate is published, so the
four premises are exactly the inputs that will remain open.

The four premises enter the proof as follows.

- Premise 1 is used in all three parts. Part (i) applies it to `P` and the opposite
  parabolic of `oppositeLeviParabolic` (through `langlandsQuotientUnique_of_inputs`). Part
  (ii) uses it through `langlandsQuotientInjective_of_secondAdjointness`. Part (iii) uses it
  through `langlandsQuotientExhaustive_of_selectedUnitaryUntwist`, which turns a selected
  tempered untwist into a surjection from the induced representation onto `π`.
- Premise 2 is used in part (i): `i_P^G(σ ⊗ ψ)` has finite length, so it has an irreducible
  quotient (through `langlandsQuotientUnique_of_inputs`).
- Premises 3 and 4 are used in part (iii) (through
  `oppositeJacquetUntwistSelection_of_inputs`). Premise 3 makes the irreducible `π`
  admissible, so its opposite standard exponents form a finite nonempty set and an exponent
  with maximal positive part exists. Premise 4 makes the opposite Jacquet module `r(π)` along
  the chosen standard parabolic of finite length. Together with the admissibility of `r(π)`,
  this gives an irreducible subrepresentation `ρ` of `r(π)` on which the split component acts
  by the chosen exponent (Renard, printed p.244 / PDF p.250). The construction then forms the
  untwist `σ = ρ ⊗ ψ⁻¹`, where `ψ` is the positive unramified character determined by the real
  part of the exponent. Since `σ ⊗ ψ ≅ ρ`, the twist `σ ⊗ ψ` embeds into `r(π)`. This
  injective map is the nonzero map into the Jacquet module that second adjointness (premise
  1) turns into a nonzero map from `i_P^G(σ ⊗ ψ)` to `π`. In the Library this is the
  structure `UnitaryUntwist` (fields `source`, `inclusion`, `untwist_eq`, `recovery`) of the
  module `OppositeJacquetUntwist`.

## Faithfulness notes

- **No change to the target.** The conclusion is the published target at the same universes
  `u, v`. Each premise is a published proposition used at the universes of its use in the
  proof. No premise mentions the specific `G`, triplet or representation of the target, so
  this is a plain implication between closed statements.
- **Universes.** Premise 1 is used at carrier universe `max u v`, the carrier universe of
  `i_P^G(σ ⊗ ψ)`. Premises 2, 3 and 4 are used at carrier universe `v`.
- **Strength.** All premises are theorems of the literature with published statements and
  their own provenance. None of them is the target or contains it. Each is the target of an
  open proof task: Task 4834 (premise 1), Task 4950 (premises 2 and 4) and Task 3838
  (premise 3).

## Provenance

Derived. The statement records which published inputs of Renard's proof of VII.4.2 remain
unproved in the represented-parabolic interface. Task 5295 (proof of
`LanglandsClassificationStatement`) welcomes such a conditional reduction as an
intermediate result. The statement lets the reduction be reviewed and published separately
from the proofs of its premises. Combining it with proofs of the four premises gives the
target.
