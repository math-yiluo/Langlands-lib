# From irreducible cuspidal summands to realizations: reduction to three inputs

Module `Langlands.Automorphic.GeneralLinearCuspidalSummandRealizationReduction`, namespace
`Langlands.Automorphic.GroupSchemeFunctions`. The module proves the implication
`GeneralLinearCuspidalSummandRealizationReductionStatement`, whose conclusion is the unchanged
`GeneralLinearCuspidalSummandRealizationStatement`. It does not prove the three premises or
assert the conclusion unconditionally. It does not address the converse direction.

## Forms attached to a summand

Use the data from `GeneralLinearCuspidalSummandRealizationStatement`. Write `Q` for the
positive-central rational quotient of the group scheme `GL_{r+1}`, `μQ` for its Haar measure,
and `S` for `fullAEL2CuspidalSubmodule` with its right action `πc`. The torus, compactness,
parabolic and measure hypotheses of the target are retained in the input statements.

`stableToContinuous` is the inclusion of stable automorphic functions into continuous rationally
invariant matrix-model functions, via their inclusion into automorphic forms. For a submodule
`A` of `Lp ℂ 2 μQ`, `summandForms F r T i A` is the submodule of stable automorphic functions
whose continuous function is cuspidal in the matrix sense and has a class in `A` according to
`IsGeneralLinearFormClass`. The latter condition includes continuous descent to `Q` and
square integrability there. For `P ≤ S` write `W(P)` for `summandForms F r T i (P.map S.subtype)`.
This carrier is an internal construction for the reduction: its definition does not assume an
identification with the smooth `K`-finite vectors of `P`.

## The three inputs

1. `GeneralLinearSummandFormsEnvelopingStatement`: for any closed `πc`-invariant `P ≤ S`, the
   genuine enveloping action on stable automorphic functions preserves `W(P)`. This is the
   differential compatibility needed by the realization, not a rapid-decay estimate. One
   route is to use square integrability of derivatives and compare differentiation of the
   translated quotient functions with differentiation in `L²`. Closedness and invariance of
   `P` then keep such derivatives inside `P`. The decay input for that route is Getz–Hahn,
   Theorem 9.7.1, p. 264 (PDF p. 276); pointwise cuspidality and comparison of the two actions
   are additional obligations, not conclusions claimed from the decay theorem alone.
2. `GeneralLinearSummandFormsDenseStatement`: if `P` is nonzero, closed and invariant, and its
   only closed invariant submodules are `0` and `P`, then every vector of `P` is in the closure
   in `S` of the classes of forms in `W(P)`. The source route is density and recovery by
   convolution in Getz–Hahn, Lemma 9.7.2, p. 264 (PDF p. 276), and the passage from finite
   Hilbert vectors to actual cusp forms in the proof of (9.40), p. 266 (PDF p. 278), using
   Lemma 9.2.3. Density of abstract finite vectors alone would not establish this input:
   the representatives must have the Library's cuspidality and stable form properties.
3. `GeneralLinearSummandFormsIrreducibleStatement`: for `P` with the same minimality conditions,
   every concrete `OperatorRealization` with carrier contained in `W(P)` is zero or has
   carrier `W(P)`. The source model is the irreducibility of `V_fin` as a
   `(𝔤,K∞) × G(𝔸_f)`-module (Getz–Hahn, Theorem 6.6.2, pp. 170–171, PDF pp. 184–185),
   together with its automorphic realization (Theorem 6.6.4, p. 172, PDF p. 186) and the
   cuspidal comparison in the proof of (9.40). A proof by that route must identify the
   relevant finite vectors and intertwine the Library's concrete operators. In particular,
   Hilbert minimality and density alone do not give algebraic irreducibility.

These are derived, Library-specific formulations of proof obligations, not verbatim
transcriptions of the cited results. For the smoothness and growth conventions, see the
[paired target statement](GeneralLinearCuspidalSummandRealizationStatement.md), especially
“Conventions: smoothness and growth”. No equivalence with Getz–Hahn's literal algebraic tensor
smoothness convention is used or asserted here.

## Implemented proof

* The lemmas for `IsGeneralLinearFormClass` preserve the relation under zero, addition,
  scalar multiplication and right translation. For translation, pullback and matrix transport
  commute with right translation, and the almost-everywhere equality transports by the
  right-invariant quotient measure. For uniqueness of the **class** of a given form, both
  quotient representatives have the same pullback, so injectivity of pullback identifies the
  representatives. Almost-everywhere equality then identifies the two `Lp` classes.
* `summandForms` is a submodule by the linear operations on the class relation and the
  cuspidal submodule property. For a stable form whose right translate is also stable,
  `summandForms_rightTranslate` uses invariance of `P` and preservation of pointwise
  cuspidality under right translation to put the translated form in `W(P)`. This applies
  to the finite and compact generators. The enveloping input treats the third family.
  `operator_invariant_iff` then gives invariance under the generated operator algebra,
  so `summandRealization` has carrier `W(P)`.
* Membership in `W(P)` supplies a class in `P`; `summandClassMap` chooses it and proves
  complex linearity by uniqueness and the additivity and scalar laws of the class relation.
  Its range is contained in the closed `P`, and every class in the density input is in its
  range by uniqueness. The density input therefore gives equality of the range closure
  with `P`. This also makes the realization nonzero, since a zero carrier would give a
  zero range and zero closure.
* For any subrepresentation, a subrepresentation of the restricted action maps along
  the inclusion to a subrepresentation of the ambient action. The carrier map is injective
  on submodules because the inclusion is injective. Thus the bottom-or-whole-carrier
  condition, together with nonzeroness, supplies `IsSimpleOrder` for the restricted
  subrepresentation lattice. Applied with the irreducibility input, this gives
  `summandRealization.IsIrreducible`. Cuspidality follows from membership in `W(P)` via
  `OperatorRealization.isCuspidal_iff`. Packaging these fields and the class map proves
  `generalLinearCuspidalSummandRealizationReduction`.

## Provenance

The implication is an internal assembly step for the summand-to-realization direction of
J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations*, GTM 300, Springer,
2024, Theorem 9.7.3, pp. 265–266 (PDF pp. 277–278), especially (9.40). The source also treats
isotypic spaces, multiplicities and the converse; none of those assertions is a conclusion
of this module. Literature ID `getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
