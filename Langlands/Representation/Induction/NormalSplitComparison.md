# Canonical normal coinvariants on a split quotient

Worker 76 constructs the outer unnormalized comparison by composing the
published normal-coinvariant and split-quotient equivalences. The parent
normalized p-adic parabolic orbit comparison remains outstanding.

The ambient group `G` is a Hausdorff topological group with the explicit
compact-open subgroup neighborhood basis. A topological group `L` has
continuous group homomorphisms `r : G →* L` and `s : L →* G` with
`r(s(l)) = l`. The subgroup `H` is closed, the kernel of `r` is closed,
and `r.ker ≤ H`. The coefficient representation `sigma` of `H` is smooth
over `ℂ`; no topology, dimension or length condition is put on its module.
The two groups and the source and target coefficient modules have independent
universes.

`compactNormalCanonicalEquiv` uses the actual map
`compactNormalCoinvariantsMap`, which takes the pointwise coefficient quotient,
and proves its bijectivity from the published
`compactInductionNormalCoinvariants`. To identify the two maps, the proof
uses induction on a coinvariant representative, extensionality of actual
compact functions, and the published family's exact evaluation formula.
`IntertwiningMap.ofBijective` then retains the canonical underlying map.
The representative formula is therefore definitional.

The coefficient quotient by `r.ker.subgroupOf H` is trivial on every element
of `H` in `r.ker`: on a representative this is precisely
`Coinvariants.mk_self_apply`. Restrict the canonical ambient equivalence
along `s`, then apply the actual `splitQuotientEquiv` to those kernel-trivial
coefficients. This defines `normalSplitCompactEquiv` from

`((compactInduced H sigma).toCoinvariants r.ker).comp s`

to

`compactInduced (H.comap s)
  ((sigma.toCoinvariants (r.ker.subgroupOf H)).comp (s.subgroupComap H))`.

It is a complex-linear, bijective `L`-intertwiner. Its actual value on a
representative `[f]` at `l` is `[f(s(l))]`. Naturality uses the actual
coinvariant maps and compact postcomposition maps. Induction on `[f]` and
pointwise extensionality reduce it to equality of `[T(f(s(l)))]`.

This is internal derived packaging of the published
`NormalCoinvariantProof` and `SplitQuotientProof`, rather than a new external
mathematical claim. Their original motivation is Bernstein–Zelevinsky,
*Induced representations of reductive p-adic groups I* (1977), §5.16,
Case IV₁, printed pages 465–466. That case moves coinvariants through
induction when the radical lies in the inducing subgroup and then uses a
complement. Here the two published comparisons are composed directly on
actual covariant compact functions and actual relation quotients. No
comparison, support preservation or bijectivity is assumed. This module has
no correction character or normalization, no compact induction in stages,
and no Case IV₂ integral.

Development compilation and Lake declaration inspection passed in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, with no warnings. Inspection of
`normalSplitCompactEquiv` retains `uG`, `uL`, and `uV`; the naturality theorem
also retains the independent `uW`. Both depend only on `propext`,
`Classical.choice`, and `Quot.sound`. These are development checks; independent
semantic review and publication remain required.
