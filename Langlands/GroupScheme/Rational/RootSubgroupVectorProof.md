# Proof of the vector and central quotient structure of relative root subgroups

Author: Worker 41.

Module `Langlands.GroupScheme.Rational.RootSubgroupVectorProof`.

## Result

`Langlands.GroupScheme.RelativeRoot.rootSubgroupVector` has type exactly
`RootSubgroupVectorStatement.{u}`, the published proposition of
`Langlands.GroupScheme.Rational.RootSubgroupStructureStatement`, at an arbitrary
universe `u`. Fix a field `k : Type u`, a group `G` over `Spec k` with
`IsConnectedReductive G`, and `i : S.toGrp ⟶ G` with `IsMaximalSplitTorus i`.
For every actual relative root `a` of `i` the theorem proves both branches:

- if `2 • a` is not a relative root, then for every representative
  `j : U ⟶ G` of `RelativeRoot.subgroup i a`, `U` is a vector group
  (`IsVectorGroup U`);
- if `2 • a` is a relative root, then `subgroup i (2 • a) ≤ subgroup i a`;
  on every test `T`, every point of `subgroup i (2 • a)` commutes with every
  point of `subgroup i a`; and every representative `j : U ⟶ G` of
  `subgroup i a` has a map `q : U ⟶ V` with
  `IsFppfQuotient ((subgroup i (2 • a)).comap j) q` and `IsVectorGroup V`.

The quotient is the fppf sheaf quotient of the statement. It identifies the
actual kernel functor of `q` with the inverse image of `U₂ₐ`, and it makes no
claim that `U(T) → V(T)` is surjective on each test. No split, quasi-split,
reducedness, perfectness or characteristic hypothesis is added. Nonreduced
relative root systems are included.

## Implemented proof

The proof is a single application of published Library theorems:

```
rootSubgroupVectorReduction
  (relativeRootSystemStatement_of_rootRankOneFactorizationStatement
    rootRankOneFactorization)
  semigroupRealization semigroupCommutator cyclicRootFunctorComparison
  cyclicWeightFiltration
```

`rootSubgroupVectorReduction`, in module `Rational.RootSubgroupVectorReduction`,
proves `RootSubgroupVectorReductionStatement.{u}`. That statement derives
`RootSubgroupVectorStatement.{u}` from five exact propositions. Each of the five
is discharged by a published unconditional theorem:

| Premise | Discharged by | Module |
| --- | --- | --- |
| `RelativeRootSystemStatement` | `relativeRootSystemStatement_of_rootRankOneFactorizationStatement rootRankOneFactorization` | `Rational.RootSystemFromFactorPairs`, `Rational.RootRankOneFactorizationProof` |
| `SemigroupRealizationStatement` | `RelativeRoot.semigroupRealization` | `Rational.SemigroupRealizationProof` |
| `SemigroupCommutatorStatement` | `RelativeRoot.semigroupCommutator` | `Rational.SemigroupCommutatorProof` |
| `CyclicRootFunctorComparisonStatement` | `RelativeRoot.cyclicRootFunctorComparison` | `Rational.CyclicRootFunctorComparisonProof` |
| `CyclicWeightFiltrationStatement` | `RelativeRoot.cyclicWeightFiltration` | `Rational.CyclicWeightFiltrationProof` |

The root-system input is the published conditional theorem
`relativeRootSystemStatement_of_rootRankOneFactorizationStatement` applied to
the published unconditional `rootRankOneFactorization`. Rank-one factorization
gives opposite factor pairs. These give integral reflection data that
centralize the full character kernel. Together with the positive-root
stabilizer theorem, the data yield `HasRelativeRootSystem i`.

The reduction uses the inputs as follows; its own Markdown has the details:

- From the root system, `HasRelativeRootSystem.nsmul_not_mem_of_three_le`
  rules out `n • a` as a relative root for every `n ≥ 3`. This is the
  crystallographic divisibility argument, with no reducedness assumption.
- The cyclic comparison identifies the first conjugation weight-filtration
  term with `subgroup i a`. For each representative, the cyclic filtration
  theorem with `r = 1` gives a represented fppf quotient by the inverse image
  of the second term, whose target has natural vector coordinates.
- If `2 • a` is absent, realization shows the second term is trivial. A
  representative is a monomorphism, so the inverse image is trivial too. The
  fppf quotient by the trivial kernel is then an isomorphism, which makes `U`
  a vector group.
- If `2 • a` is present, realization, the commutator bound and the cyclic
  comparison give the inclusion `U₂ₐ ≤ Uₐ` and commutation on all tests. The
  absence of weights `n • a` with `n ≥ 3` identifies the second filtration
  term for `a` with the first term for `2 • a`. The cyclic comparison for
  `2 • a` identifies that term with `subgroup i (2 • a)`. The cyclic quotient
  is therefore the required
  fppf quotient by `(subgroup i (2 • a)).comap j`.

## Sources

The statement follows Kaletha–Prasad (2023), §2.6.8 and Proposition 2.11.14,
and Conrad–Gabber–Prasad, second edition (2015), Lemma 3.3.8, as cited in the
statement's Markdown. As usual for proofs, this one runs through the Library's
own published theorems rather than reproducing the printed arguments.

The composition used for the root-system input is the one in Worker 23's
staged, still unpublished candidate `49803ae2-9303-4835-94e0-62e7a50a3dd4`
for task `51ecd216-d68e-4f71-afeb-6d7ff3683ec9`. This module does not import
that candidate. It applies the two published theorems directly.
