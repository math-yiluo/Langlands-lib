# Minimal normal almost-simple factors from actual-root premises

For an algebraically closed field `k : Type u` of arbitrary characteristic,
`NormalAlmostSimpleFactor G` records an actual group scheme, an actual closed
inclusion into `G`, the published corrected `IsAlmostSimple` property of the
source, and normality of its range on every test scheme.

`normalAlmostSimpleFactorOfActualRoots` constructs this data for a semisimple
`G` whose identity inclusion has nontrivial full range. Three structural
propositions remain explicit premises: `NormalReductiveCenterStatement`,
`SemisimpleRootGenerationStatement`, and
`SemisimpleNormalRootDichotomyStatement`. The companion existence theorem
establishes the same construction before classical choice.

The implementation first proves that a nontrivial semisimple group is
noncommutative. If it were commutative, its identity would factor through its
finite full centre. That factor is a closed immersion, so the group itself
would be finite. The existing finite-target rigidity theorem for smooth
connected reduced groups over an algebraically closed field then identifies
its identity map with the unit map, contradicting nontriviality on all test
schemes.

The second helper transfers normality from a closed normal subgroup `K` of a
smooth connected closed normal subgroup `H` to the ambient semisimple group.
The closed normalizer of `K` in `G` contains `H` by internal normality and the
full scheme-theoretic centralizer of `H` by commutation. The conditional
root-to-centralizer generation theorem makes this normalizer the entire
ambient group. This argument retains every test scheme and every refinement;
it does not require smoothness or connectedness of `K`.

For the factor construction, the proof chooses an actual maximal torus using
the published existence theorem. The published finite-Galois splitting theorem
and algebraic closedness make it split. It then minimizes the natural-number
Lie dimension among nontrivial closed connected reductive normal subgroups of
`G`. The identity inclusion witnesses that this collection is nonempty.
The chosen subgroup is semisimple by the conditional normal-subgroup
finite-centre construction, and hence noncommutative by the first helper.
For each smooth connected closed normal subgroup `K` of this chosen subgroup,
trivial range gives the first alternative in `IsAlmostSimple`. Otherwise,
normality transfer makes `K` normal in `G`. The published normal-subgroup
reductivity theorem puts `K` in the minimizing collection. Minimality rules
out strict Lie-dimension decrease; the published proper-closed-subgroup
inequality therefore makes its inclusion an isomorphism, with full range on
all test schemes. This supplies the second alternative.

The provenance is an internal composition of the named published interfaces,
natural-number minimization, and classical choice of actual representatives.
The new construction and its helper theorems are conditional. They do not prove
any of the three structural propositions, generation by all normal almost-simple
subgroups, or the host task's exact unconditional generation statement.
