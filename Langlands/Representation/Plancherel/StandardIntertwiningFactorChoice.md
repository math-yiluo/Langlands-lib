# Auxiliary choices in normalized intertwining factors

This internal construction specializes the published
`IsCompatible.compactOpenFactorMeasure_eq_of_localProducts` to the two actual
complement measures already used in standard-intertwining composition. It
introduces no new generic uniqueness theorem. Waldspurger (2003), IV.1,
printed p.279 (PDF p.45), motivates the ordered complement coordinates;
IV.1(12), printed p.283 (PDF p.49), is the eventual distance-additive
composition assertion. This auxiliary result concerns measures in supplied
coordinates, not that full assertion.

Fix `D : OrderedSubgroupFactorization U₀ U₁ U₂ V W`. In the middle
intersection `I = U₁.subgroupOf U₂`, let
`H = (U₀.subgroupOf U₂).subgroupOf I` and
`K = (V.subgroupOf U₂).subgroupOf I`. The existing
`intersectionSubgroupProduct` is literal ordered multiplication `H × K → I`.
Hold the regular Haar measures on `I` and `H` fixed, and supply one compatible
Weil measure on the actual quotient `H \ I`. Suppose `I` is locally compact,
`G` is Hausdorff, `H` is closed in `I`, and all displayed groups and quotients
carry Borel structures. The kernel Haar measure is also right invariant.

Choose either regular two-sided seed Haar measure on `K`, and independently
choose compact open subgroups `S` of `I` and `B` of `K`. Each pair must satisfy
its own literal local product identity
`intersectionSubgroupProduct '' ((H ∩ S) × B) = S`.
`intersectionNormalizedFactor_eq_of_localProducts` proves that the two
constructed measures on the original carrier `V` are equal. The published
generic comparison identifies both measures on `K` with the inverse-chart
pushforward of the same compatible Weil measure. Applying the same
`intersectionComplementEquiv` pushforward yields equality on `V`.

`secondNormalizedFactor_eq_of_localProducts` does the corresponding
comparison on `W`. Here the fixed ambient group is `U₂`, the closed kernel is
`U₁.subgroupOf U₂`, and the actual complement is `W.subgroupOf U₂`.
The two compact-open pairs must each satisfy their own literal local product
identity for `secondSubgroupProduct`. The fixed ambient and kernel measures,
a common compatible Weil measure, local compactness, regular Haar measures,
right invariance on kernel and both seed measures, and displayed Borel
structures are retained. Equality is transported through the existing
`secondComplementEquiv`.

The definition `normalizedComplementProductMeasure` is the product on
`V × W` of the previously defined `intersectionNormalizedFactor` and
`secondNormalizedFactor`. The theorem
`normalizedComplementProductMeasure_eq_of_localProducts` applies both
comparisons to prove that this ordered product measure is unchanged when
both seeds and both compact-open pairs vary independently. It uses the
respective local product identity for every pair. No product regularity,
S-finiteness or second countability is needed for these measure equalities.
Those hypotheses remain where required by the existing Fubini and
composition results.

The ambient and kernel measures, underlying subgroups and literal charts
are fixed. This does not compare different source Haar normalizations or
construct any compatible Weil measure, compact-open local geometry, or
reductive chart. The source has the first complement before the second in
the integrand; these products keep that order and assert no commutation or
product-group homomorphism. Actual integral representability, convergence,
rational continuation and every whole-task Plancherel completion condition
remain open. The existing explicit operator pause on root-product geometry
is unaffected.
