# Locally normalized factors and actual standard-integral composition

This is an internal derived construction for the ordered coordinates motivating
Waldspurger IV.1, printed p.279 / PDF p.45, and the composition identity
IV.1(12), printed p.283 / PDF p.49, in *La formule de Plancherel pour les
groupes p-adiques (d'après Harish-Chandra)* (2003). It applies the existing
intersection normalization to actual quotient measures and standard integrals.
It does not establish existence of the reductive charts or analytic
continuation.

## Actual second factor and its measure

Retain the original actual subgroups and the three literal homeomorphisms
`D : OrderedSubgroupFactorization U₀ U₁ U₂ V W`. Write
`I₂₀ = U₀.subgroupOf U₂`, `I₂₁ = U₁.subgroupOf U₂`,
`H = I₂₀.subgroupOf I₂₁`, `K = (V.subgroupOf U₂).subgroupOf I₂₁`
and `L = W.subgroupOf U₂`. These are actual subgroups with inherited
topologies. The arbitrary ambient universe is retained.

`secondComplementEquiv` identifies `L` with `W` by the supplied inclusion.
`secondSubgroupProduct` composes this equivalence with `D.second`; its formula
is literal multiplication `i * l` inside `U₂`. There is no assertion that an
ordered product homeomorphism is a group homomorphism.

For independent measures `μU₂`, `μI₂₁`, `μL`, an open subgroup `T` of `U₂` and
an open subgroup `C` of `L`, `secondNormalizedFactor` is the pushforward to
`W` of

`compactOpenFactorMeasure I₂₁ L μU₂ μI₂₁ μL T C`.

Under the Haar, closedness and compactness hypotheses below, all three
compact-open masses are strictly positive and finite. The scalar is their
nonnegative-real ratio
`μU₂(T) / (μI₂₁(I₂₁ ∩ T) μL(C))`, using the existing nonnegative-real
construction. The definition does not depend on a quotient measure.
Regularity, S-finiteness and right invariance transport from `μL`; under the
displayed Haar, closed-intersection and compactness conditions the measure
is Haar. The two existing intersection measures also acquire right-invariance
instances by the published continuous group-equivalence transport theorem.
No ambient Haar measure is restricted to a potentially null subgroup.

`measurePreserving_second_of_localProduct` assumes a Hausdorff topological
ambient group, locally compact `U₂`, regular Haar `μU₂`, regular two-sided
S-finite Haar `μI₂₁` and `μL`, regularity of their product, the individual
Borel structures and both displayed product Borel structures, a compatible
Weil measure on `I₂₁ \ U₂`, closedness of `I₂₁`, compactness of `T` and `C`,
and the actual local product identity

`secondSubgroupProduct '' ((I₂₁ ∩ T) × C) = T`.

The compact-open normalization theorem first gives exact preservation on
`I₂₁ × L`. The product pushforward identity then transports it to `I₂₁ × W`.
The full second product identity is a conclusion.

## Composite and quotient normalizations

`measurePreserving_normalizedProducts` combines this result with
`measurePreserving_intersectionFirst_of_localProduct`. It assumes compact-open
product geometry inside `I₂₁` for `H × K` and inside `U₂` for `I₂₁ × L`,
compatible Weil measures for `H \ I₂₁` and `I₂₁ \ U₂`, and the displayed
regular two-sided S-finite Haar measures and seed-product regularity.
The individual and four product Borel structures are explicit.
The ambient group is locally compact and Hausdorff, and `U₀`, `U₁`, `U₂`
are closed. The proof derives local compactness of `U₂` and `I₂₁` and
closedness of `I₂₁` and `H` by continuous subtype preimages.

With `μI₂₀` the transported `intersectionKernelMeasure`,
`μV` the `intersectionNormalizedFactor` and `μW` the `secondNormalizedFactor`,
the conclusions are precisely

`MeasurePreserving D.second (μI₂₁.prod μW) μU₂` and
`MeasurePreserving D.composite (μI₂₀.prod (μV.prod μW)) μU₂`.

Neither identity, nor restricted-first product preservation, is supplied
as a premise. Associativity of the ordered charts and of product measures
gives the composite conclusion from the two locally derived identities.

`measurePreserving_quotientCoordinates_of_localProducts` additionally assumes
the original first product identity for `μI₁₀.prod μV`, the other two
compatible quotient measures, regular two-sided S-finite Haar `μI₁₀`,
a measure finite on compacts on `U₁`, regularity of `μV.prod μW`, and the
additional individual and quotient Borel structures, including `V × W`.
It derives all three original quotient-coordinate preservation identities
using the newly constructed measures and the existing compatible-Weil
quotient comparison.

## Actual integral composition and retained obligations

`comp_hasIntegral_of_localProducts` applies those quotient identities to the
existing `HasIntegral.comp_ordered`. It retains the ambient nonarchimedean
group condition, the two actual semidirect decompositions, the canonical
`SmoothRep` on their common Levi (with arbitrary representation-carrier
universe), the two actual standard-integral witnesses, and the displayed
`OrderedScalarIntegrable` condition. Its conclusion is the actual composite
standard-integral witness with the endpoint quotient measure.

The original first chart still requires its exact product normalization
with the constructed `μV`. The compatible Weil measures and all displayed
regularity, Borel, Haar and local product conditions remain application
obligations. Comparison with separately prescribed source Haar measures,
reductive chart existence and root-distance geometry, convergence and
rational continuation are not proved here. This focused conditional
construction closes no whole-program Plancherel completion condition.
