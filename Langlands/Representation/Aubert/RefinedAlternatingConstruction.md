# Conditional alternating sums inside an actual product Levi

Author: Worker 320.

This is an internal construction from the published actual refinement functors,
the published preservation proposition, and the universal property of the exact
finite-length smooth Grothendieck group. Every K0 map and alternating operator
in this module takes an explicit proof

```lean
h : Parabolic.NormalizedRefinedFiniteLengthExactnessStatement.{uF, max uF uV} F T
```

as an argument. The module constructs no such proof. Its results remain
conditional until the separate preservation theorem is available. The suffix
`Of` records that dependency in the public names.

## Objects, universes and maps

The parameters are arbitrary `{p : ℕ} [Fact p.Prime]`,
`F : PadicField.{uF} p` and supplied `T : F.TopologicalData`, with independent
`uF` and `uV`. The only topology installed is `T.topology`. Representation
carriers lie in `Type (max uF uV)`. The assertions include every rank `n`,
outer shape `B : GeneralLinear.BlockShape n`, and actual ordered refinement
`S : Geometric.BlockRefinement B`, including rank zero.

Write `M = B.Levi F.Carrier` and
`M_S = Geometric.refinedLevi F.Carrier B S`. The latter is the actual subgroup
of the product Levi, rather than a replacement abstract group. The source
and target groups are the published exact Grothendieck groups of all smooth
complex representations of finite group-algebra length. Their relations come
from all actual short exact sequences, including nonsplit sequences.
No tensor decomposition, admissibility or finite complex dimension premise is
added.

In namespace `Langlands.Parabolic`,
`normalizedRefinedInductionK0Of F T h B S` maps the exact K0 of `M_S` to that
of `M`, and `normalizedRefinedJacquetK0Of F T h B S` maps in the other
direction. Both use `SmoothRep.FiniteLengthGrothendieckGroup.map` on the
unchanged functors at `.{uF, max uF uV}`:

- induction uses `T.normalizedRefinedInductionFunctor B S`, with finite-length
  clause `h.1 n B S` and short-exact clause `h.2.2.1 n B S`;
- Jacquet uses `T.normalizedRefinedJacquetFunctor B S`, with finite-length
  clause `h.2.1 n B S` and short-exact clause `h.2.2.2 n B S`.

The functors retain positive half-modulus covariance and right translation
for induction, and the inverse half-modulus action on actual upper-unipotent
coinvariants for Jacquet. This module changes neither normalization nor maps.
The two `*_finiteLengthClass` theorems compute each K0 map on every actual
finite-length object, with any proof of finite length for its actual output.
They follow directly from the generic functor-map computation theorem and
proof irrelevance.

## The finite sum

In namespace `Langlands.Aubert`, `refinementSignExponent B S` is

```text
sum_i (B.size i - (S i).length).
```

The theorem `refinementSignExponent_eq` proves that this is also
`n - sum_i (S i).length`. It uses `(S i).length_le`, distributivity of natural
subtraction over a finite sum under those inequalities, and `B.sum_eq`.
Thus subtraction in each summand has its ordinary nonnegative meaning.
For the root system of a product of general linear groups this counts the
simple roots retained within each refined block. This explanatory root
interpretation is not a separate Lean theorem.

The conditional definition `alternatingOperatorOnLeviOf F T h B` is the
integer-linear endomorphism of the exact K0 of `M` given by

```text
sum_S (-1)^(refinementSignExponent B S) *
  (normalizedRefinedInductionK0Of F T h B S) ∘
  (normalizedRefinedJacquetK0Of F T h B S).
```

The sum runs over all actual refinements exactly once. Its enumeration is
`Fintype.ofFinite`: a refinement is a finite dependent product of block-shape
types, each finite by the published `finiteBlockShape` instance. There is no
extra finiteness assumption. The theorem `alternatingOperatorOnLeviOf_eq_sum`
exposes the sum for any enumeration; it uses subsingleton uniqueness of
`Fintype`. The theorem `alternatingOperatorOnLeviOf_apply` evaluates it on
any virtual class by linear-map evaluation.

`refinedInductionJacquet_hasFiniteLength_of` supplies finite length of actual
induction after actual Jacquet restriction by applying the two clauses of
`h` successively. The theorem
`alternatingOperatorOnLeviOf_finiteLengthClass` evaluates the operator on the
class of any actual finite-length smooth representation of `M`: it is the
same signed sum of the classes of its actual induction-after-Jacquet objects,
for any chosen output-length proofs. The proof expands the sum and applies
the two map computations to each summand.

For rank zero the outer shape is empty and has a unique empty refinement;
the exponent is an empty sum, hence zero. The construction includes this case
without a positive-rank hypothesis. No identification of its operator with
an identity map is asserted.

## Provenance and scope

This is a derived, source-free formal construction from
`Parabolic.RefinedFiniteLengthFunctorStatement`,
`Smooth.FiniteLengthGrothendieckFunctor`, and
`CuspidalSupport.FiniteBlockShapes`. Its intended use is to formulate later
identities between the already defined alternating sum on `GL_n` and sums
inside actual product Levis. The sign is the factorwise version of the
published `Aubert.AlternatingOperator` convention. No numbered literature
assertion is transcribed or used as a proof.

The construction proves no finite-length preservation or exactness assertion,
and proves no comparison with the GL operator, commutation, involutivity,
irreducible image or analytic classification. In particular its explicit
argument `h` must not be suppressed when using these results. The existing
functor, preservation-statement, exact-K0 and GL-operator pairs remain
unchanged.

## Development checks and independence

Development compilation `5b088082-928b-4dac-b324-42c933bfeebe` returned zero
errors and zero warnings. Inspection `af245c3f-86ac-4e49-a606-edaebea1c379` of
`Langlands.Aubert.alternatingOperatorOnLeviOf` reports a definition with
independent universe parameters `[uF, uV]`, using only `propext`,
`Classical.choice` and `Quot.sound`. These are development results, not
independent semantic acceptance.

A recursive audit of the actual project import lines finds 38 modules,
including this module, with no missing project imports. They comprise the
local-field and GL definitions and normalization, smooth categories, twists,
coinvariants, actual refinement-functor definitions, the refinement
preservation proposition, finite block enumeration, and the generic exact K0
construction. There is no classification or analytic representation-theory
proof in that closure. A search of those sources for the excluded parent and
downstream classification declarations returns no matches. The private audit
is `.private/notes/refined-alternating-import-audit.json`. The separate
refinement-preservation proof is not an imported or proved input.
