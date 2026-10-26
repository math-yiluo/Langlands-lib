# Compact induction commutes with normal coinvariants

Worker 182 proves the published proposition
`Langlands.Induction.CompactInductionNormalCoinvariants.{uG,uV}` as
`Langlands.Induction.compactInductionNormalCoinvariants`. The statement and
every imported Lean/Markdown pair are preserved.

## Exact scope and maps

The public theorem has exactly the published proposition as its type, without
additional parameters. Thus it retains independent group and coefficient
universes, a Hausdorff topological group with the stated compact open
neighborhood basis, closed subgroups `H,N` with `N` normal in `G` and `N ≤ H`,
and every object of `Langlands.SmoothRep.{0,uG,uV} ℂ H`. Coefficient modules
have no additional topology, dimension, admissibility, or length restrictions.

For `sigma = A.representation`, the proof constructs one family of actual
ambient `G`-representation equivalences

```text
e_A : (compactInduced H sigma).toCoinvariants N
        ≃ compactInduced H (sigma.toCoinvariants (N.subgroupOf H)).
```

Its underlying map is the published
`compactNormalCoinvariantsMap H N hNH sigma`, which descends
`compactInducedMap H (sigma.toCoinvariantsMkQ (N.subgroupOf H))`.
The carriers are the existing `CompactFunctions` and Mathlib coinvariant
relation quotients. The induced action remains right translation and the
covariance convention remains `f(h*g) = sigma(h)(f(g))`.

The same family satisfies the exact representative formula

```text
eval H sigma_N (e_A [f]).val g = [eval H sigma f.val g]
```

and the naturality equation in the target for every morphism `T : A ⟶ B`.
The quotient maps on morphisms are the actual `Coinvariants.map` after
restriction, and postcomposition is the actual `compactInducedMap`.

## Implemented proof

Three private lemmas separate the algebraic assembly from the published
topological prerequisites.

The injectivity lemma takes the implication from pointwise coefficient
relation-kernel membership to membership in the induced relation kernel.
For a coinvariant class whose image is zero, coinvariant induction chooses a
representative `f`. Evaluating the zero image at each `g` and using
`Coinvariants.mk_eq_zero` shows that every coefficient `f(g)` lies in its
relation kernel. The implication puts `f` in the induced relation kernel,
so its coinvariant class is zero. The linear-map criterion for injectivity
then proves injectivity of the canonical map.

The surjectivity lemma takes surjectivity of compact postcomposition by the
coefficient quotient. For a target compact function it chooses a compact
lift `f`; the class `[f]` maps to that function by the defining representative
identity of the canonical map.

The family lemma applies these two lemmas for every smooth object `A` and
uses `IntertwiningMap.ofBijective` to turn the canonical map into an actual
representation equivalence. The equivalence has the same underlying map.
Consequently `compactNormalCoinvariantsMap_eval` proves the representative
formula, and `compactNormalCoinvariantsMap_natural`, specialized to
`SmoothRep.hom T`, proves naturality of that very family.

The public theorem supplies both premises from published proofs. First it
derives compact open subgroup cofinality by applying the given neighborhood
basis to the underlying open set of each open subgroup. For each `A`, let
`q = A.representation.toCoinvariantsMkQ (N.subgroupOf H)`. This is the
actual coefficient quotient, is surjective by `Coinvariants.mk_surjective`,
and has its coefficient carrier in `Type uV`. The target quotient
representation is smooth by the published `isSmooth_of_surjective`, applied
to `q`, its surjectivity, and `A.isSmooth`. The theorem
`compactInductionSurjectivity` now gives surjectivity of
`compactInducedMap H q`.

For the injectivity premise, the reverse implication of the published
`compactInductionNormalCoinvariantKernel` gives the required induced
relation-kernel membership from the pointwise condition. It is applied with
the original basis, closedness, normality, containment, and smoothness
hypotheses. Both premises of the family lemma are therefore discharged by
theorems, leaving exactly the original proposition.

## Provenance and dependencies

This is an internal derived assembly from the published modules
[`NormalCoinvariantMap`](NormalCoinvariantMap.md),
[`CompactSurjectivityProof`](CompactSurjectivityProof.md),
[`NormalCoinvariantKernelProof`](NormalCoinvariantKernelProof.md), and
[`Smooth.Transfer.SubquotientProof`](../Smooth/Transfer/SubquotientProof.md).
The first supplies the canonical map and its two identities. Compact
surjectivity uses a smooth lift followed by a cutoff on the actual compact
projected support. The kernel theorem proves the actual relation-span
identity using compact local sections, conjugation and finite patching.
The smooth quotient transfer supplies the smoothness needed for the
coefficient quotient. These are imported proofs, with no new exactness,
lifting, kernel, or averaging assumption in the public theorem.

The target's original source is I. N. Bernstein and A. V. Zelevinsky,
*Induced representations of reductive p-adic groups I*, Ann. Sci. ENS (4)
10 (1977), 441–472, §5.16, Case IV₁, printed pages 465–466 / PDF pages 26–27.
The registered literature ID is `bernstein-zelevinsky-1977-induced-i`; the
retained original is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`,
SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
That section, including its reduction diagram and continuation, was read in
full during this task; no source-specific project errata was found.

In the source, `V ⊆ M = P` corresponds to `N ≤ H`, with trivial `U`,
`Q = G`, and trivial character. Normality makes `N` act trivially on
`H \ G`; the source uses localization of compact sections and equivariant
sheaf reconstruction to obtain its comparison. The implemented proof instead
uses the published compact lifting and relation-kernel theorems to establish
bijectivity of pointwise passage to coefficient coinvariants. The target is
the same-ambient, unnormalized formulation documented in
[`NormalCoinvariantStatement`](NormalCoinvariantStatement.md).
Complement restriction, normalization and §5.17's quotient integration are
separate results.
