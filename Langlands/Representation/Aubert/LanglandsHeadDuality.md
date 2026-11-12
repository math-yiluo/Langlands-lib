# Langlands heads as Aubert duals of Zelevinsky labels

Module `Langlands.Representation.Aubert.LanglandsHeadDuality`, namespace
`Langlands.Aubert.LanglandsHeadDuality`.

Author: Worker 186.

This helper module serves the proof of Tadić's Proposition A.4(ii)
(`Langlands.Classification.langlandsHeadProductSubquotient`, in
[LanglandsHeadProductSubquotientProof](../Classification/LanglandsHeadProductSubquotientProof.md)).
It proves the following in the graded Grothendieck group
`GradedGrothendieckGroup.{uF, uV} F T`:

1. The support-adjusted graded Aubert operator `t = gradedAdjustedOperator F T`
   permutes the irreducible basis classes and is multiplicative.
2. Zelevinsky labels are unique, and every multisegment has one.
3. `t` sends the label of a multisegment `a` to the class of every Langlands head
   of `a` (Theorem P below).
4. The label of `a + b` occurs in the product of the labels of `a` and `b`, which is
   the Grothendieck-group form of Zelevinsky 1980, Proposition 8.4, restricted to
   multiplicity at least one.

Every result is unconditional. The module states no `Prop` definition and adds
no axiom. The hypotheses
`hx : BinaryProductExactnessStatement.{uF, uV} F T` and
`hl : GradedInductionRingLawsStatement F T hx` appear only as section variables,
because the ring structure `gradedInductionRing F T hx hl` and `zeta F T hx hl`
depend on them. Both are proved in the Library (`binaryProductExactness`,
`gradedInductionRingLaws`), and the final proof supplies those proofs. Some results
also take a unitary additive character `ψ`. The final proof obtains `ψ` from
`HarmonicAnalysis.padicUnitaryAdditiveCharacterExists`.

## Notation from the Library

These definitions are all published in
[SegmentPolynomialSurjectivity](SegmentPolynomialSurjectivity.md) and the modules
it imports.

- `Label F T m` is the type of isomorphism classes of irreducible smooth
  representations of `GL_m(F)`. `basisClass F T m c` is the class of `c` in rank `m`.
  `coeff F T m c x` is the multiplicity of `c` in the rank-`m` component of `x`.
  `IsEffective F T x` says that every coefficient of `x` is nonnegative.
- `zeta F T hx hl a` is Zelevinsky's `π(a)` in the Grothendieck group. It is the
  product of the classes `gradedSegmentSocle Δ` of the segment representations
  `⟨Δ⟩` over the segments of `a`, so `zeta (a + b) = zeta a * zeta b` (`zeta_add`).
- `IsLabel F T a m c` means that some representative of `c` is an irreducible
  subrepresentation of a precedence-ordered product of segment socles with
  multisegment `a`. This is a weak form of Zelevinsky's `⟨a⟩`.
- `Multisegment.RankLE b a` is the rank order of
  [MultisegmentRankOrder](MultisegmentRankOrder.md). It holds when `b` and `a` have
  the same cuspidal content and each segment is contained in at most as many
  segments of `a` as of `b`. Its strict part is well-founded
  (`Multisegment.wellFounded_rankLT`).
- `a.IsLanglandsHead π`, from
  [LanglandsData](../Classification/LanglandsData.md), says that `π` is the
  irreducible head of a nonprecedence-ordered product of segment heads (essentially
  square-integrable special representations) with multisegment `a`.

## Contents

### Coefficients and effective products

- `apply_eq_of_basisClass` says that two `ℤ`-linear functionals agreeing on every
  basis class occurring in `x` agree on `x`. `basisClass_injective` is
  injectivity of `basisClass` in each rank.
- `gradedInclusion_mul_gradedInclusion`: for actual finite-length `A` and `B`, the
  product of their classes is the class of the actual normalized product
  `T.binaryNormalizedProductFunctor m n` of `(A, B)`. It comes from
  `gradedMultiplication_homogeneous` and `binaryProductK0_classes`.
- `isEffective_basisClass_mul` and `isEffective_mul`: products of effective classes
  are effective. Both factors are expanded in basis classes, and each product of
  basis classes is the class of an actual representation.

### The adjusted operator on irreducible classes

- `adjustedOperator_irreducible_eq`: for an irreducible `π`, the adjusted operator
  sends the class of `π` to the class of an irreducible `πD`, with sign `+1`. The
  published `irreducibleImage` gives `alternatingOperator [π] = ±[πD]`. The support
  sign is then identified by `supportSign_eq_of_effective`.
- `gradedAdjustedOperator_basisClass`: `t` sends every basis class to a basis class
  of the same rank.
- `coeff_gradedAdjustedOperator`: if `t (basisClass m c) = basisClass m c'`, then
  `coeff m c' (t x) = coeff m c x` for all `x`. Since `t` is an involution
  (`adjustedInvolutivity`), it permutes the basis classes.

### Products of segment heads

- `gradedInclusion_induced_eq_prod_gradedSegmentSpecial`: the class of a product
  `d.induced` of segment heads is `∏ i, gradedSegmentSpecial (d.segments i)`. The
  proof is an induction on the number of segments. It uses the head/tail binary
  splitting `SegmentProductSplit.nonempty_iso_binary`, with the rank-zero case
  handled by `SegmentProductOrderedAssembly.zeroDatumUnitIso`. Finite length of
  such products is `hasFiniteLength_induced_of_irreducible`, from the published
  `irreducibleProductFiniteLength`.
- `adjustedRingHom` is `t` as a ring endomorphism, built by `gradedOperatorRingHom`
  from `adjustedHomogeneousMultiplicativity` and `gradedAdjustedOperator_unit`.
  The lemma `gradedAdjustedOperator_mul` gives `t (x * y) = t x * t y`.
- `gradedAdjustedOperator_gradedSegmentSpecial`: `t` sends the special class of a
  segment to its socle class. This follows from `adjustedSegmentExchange` and
  involutivity.
- `gradedAdjustedOperator_headInduced`: for a product `d.induced` of segment heads,
  `t [d.induced] = zeta (d.multisegment)`.

### Labels

- `coeff_zeta_eq_one_of_isLabel`: a label of `a` occurs in `zeta a` with
  multiplicity exactly one.
- `isLabel_unique`: two labels of `a` in the same rank are equal.
- `exists_isLabel_of_degree`: every multisegment `a` has a label in rank
  `a.degree`. It comes from `multisegmentConstituentDataExistence` and
  `orderedMultisegmentSocleExistence`.

The first two follow from the published bound `labelCount_zeta_le_one` (the
weighted count of all labels of `a` in `zeta a` is at most one) and
`one_le_coeff_zeta_of_isLabel`.

`isIrreducible_of_isLanglandsHead` and `degree_of_isLanglandsHead` unpack the head
relation.

### Theorem P: Langlands heads are duals of labels

- `coeff_zeta_pos_of_isLanglandsHead`: if `π` is a Langlands head of `a` and
  `t [π] = basisClass m c'`, then `c'` occurs in `zeta a`. The class `[π]` occurs in
  `[d.induced]` because `π` is a quotient of it. Applying
  `coeff_gradedAdjustedOperator` and `gradedAdjustedOperator_headInduced` turns this
  into an occurrence of `c'` in `zeta a`.
- `gradedAdjustedOperator_label`: if `c` is a label of `a` and `π` is a Langlands
  head of `a`, then `t (basisClass m c) = basisClass m [π]`. The proof is a
  well-founded induction on `a` along the strict rank order. Let `t [π] = c'`, and
  let `b` be a label multisegment of `c'`, which exists by
  `multisegmentSocleExhaustion`. By the previous item and
  `rankLE_of_coeff_zeta_pos` (Zelevinsky's triangularity), `RankLE b a`. Suppose
  `b ≠ a`. Then the induction hypothesis, applied to `b` and a Langlands head `πb`
  of `b` (`multisegmentHeadExistence`), gives `t c' = [πb]`. But `t c' = [π]`, so
  `π ≅ πb`, and `multisegmentHeadClassification` forces `a = b`, a contradiction.
  Hence `b = a`, and `isLabel_unique` gives `c' = c`.

### Zelevinsky's Proposition 8.4 for labels

- `exists_coeff_pos_mul_right` and `exists_coeff_pos_mul_left`: a positive
  coefficient of a product with an effective factor comes from a basis class
  occurring in that factor.
- `isEffective_mul_sub_basisClass_mul`: if `X` occurs in the effective `u` and `Y`
  occurs in the effective `v`, then `u * v - X * Y` is effective.
- `isLabel_of_coeff_basisClass_mul_pos`: suppose the label of `a + b` occurs in
  `X * Y`, where `X` occurs in `zeta a` and `Y` occurs in `zeta b`. Then `X` is a
  label of `a` and `Y` is a label of `b`. Let `a'` and `b'` be the label
  multisegments of `X` and `Y`. Triangularity gives `RankLE a' a` and `RankLE b' b`.
  The label of `a + b` occurs in `zeta (a' + b') = zeta a' * zeta b'`, so also
  `RankLE (a + b) (a' + b')`. Containment counts are additive, so all three
  inequalities are equalities, and hence `a' = a` and `b' = b`.
- `one_le_coeff_label_mul`: let `ca`, `cb` and `cab` be the labels of `a`, `b` and
  `a + b`. Then `1 ≤ coeff (m + n) cab (basisClass m ca * basisClass n cb)`. Write
  `zeta (a + b) = ca * cb + ca * (zeta b - cb) + (zeta a - ca) * zeta b`. Both
  correction terms are products of effective classes. By the previous item and
  label uniqueness, neither term contains `cab`. Since `cab` occurs in
  `zeta (a + b)`, it occurs in `ca * cb`.

## Provenance

This module is internal and derived. It formalizes no single statement of the
literature. Its ingredients are as follows.

- Zelevinsky 1980 (`zelevinsky-1980-induced-ii`), Theorem 7.1: triangularity of
  `⟨b⟩` in `π(a)` and multiplicity one of `⟨a⟩`. The Library proves it in the
  rank-order form `rankLE_of_coeff_zeta_pos` and `labelCount_zeta_le_one`. Label
  existence and uniqueness, for the weak labels above, are the parts of
  Theorem 6.1(a) used here.
- Zelevinsky 1980, Proposition 8.4, printed p.196 (PDF page 33): `⟨a_1 + ⋯ + a_p⟩`
  occurs in `⟨a_1⟩ × ⋯ × ⟨a_p⟩` with multiplicity one. Only the binary case with
  multiplicity at least one is proved here (`one_le_coeff_label_mul`), in the
  Grothendieck group. Zelevinsky's proof uses highest derivatives (Theorem 8.1).
  The proof here instead uses the triangularity of Theorem 7.1 together with
  `zeta_add`.
- Aubert 1995 (`aubert-1995-duality`), Theorem 2.3, and Zelevinsky's involution
  (Zelevinsky 1980, §9.12). The support-adjusted operator is a multiplicative
  involution that sends irreducible classes to irreducible classes. On segments it
  exchanges the segment class `⟨Δ⟩` with the special class of `Δ`. The Library
  proves these facts (`irreducibleImage`, `adjustedHomogeneousMultiplicativity`,
  `adjustedInvolutivity`, `adjustedSegmentExchange`), and this module only uses
  them.
- Rodier 1982 (`rodier-1982-gln`), §4.3 Theorem 3: existence and classification of
  Langlands heads of multisegments (`multisegmentHeadExistence`,
  `multisegmentHeadClassification`).

Theorem P, `t ⟨a⟩ = L(a)`, is the standard comparison between the Zelevinsky and
Langlands classifications through the Aubert–Zelevinsky involution. Its induction
on the rank order is proved here and does not follow a particular printed proof.
