# Composition of actual standard integrals with a common Levi

Worker 241, with Worker 360 contributing the paired local product module.

`conditionalDynamicCommonLeviComposition` proves exactly
`Langlands.Plancherel.DynamicCommonLeviComposition.ConditionalDynamicCommonLeviCompositionStatement.{u, uV}`.
It imports the published statement by Lean name and preserves its hypotheses,
arbitrary universes, and arbitrary characteristic. The group need not be split
or quasisplit. The structural factorization statement remains the premise
already present in the target.

## Source and scope

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333,
DOI 10.1017/S1474748003000082, registered as
`waldspurger-2003-plancherel`, PDF SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The standard integral is in IV.1, printed p.278 (PDF p.44); the ordered-product
and Fubini argument occurs on printed p.279 (PDF p.45); formula IV.1 (12)
is on printed p.283 (PDF p.49).

The theorem proves the Library's conditional, pointwise form of (12), on the
intersection of the three full convergence regions. It retains the three
squared-modulus identities, two compact-open splittings, common-centralizer
equalities, distance condition, and structural premise supplied by the published
statement. It asserts neither convergence-region nonemptiness nor rational
continuation. Its internal measure lemmas are derived from the published source
normalization and quotient-integration results; they are implementation steps
for this conditional statement, rather than additional assertions from the paper.

## Structural and local product inputs

Write `Uᵢ = radical ψᵢ`, `V = U₁ ∩ oppositeRadical ψ₀`, and
`W = U₂ ∩ oppositeRadical ψ₁`. Transitivity of the common-centralizer equalities
puts the triple in the form required by the structural premise. Applying that
premise to `hG` and the distance condition gives a witness
`D : OrderedSubgroupFactorization U₀ U₁ U₂ V W`. No structural theorem is
postulated or proved anew.

The imported supporting pair `DynamicCommonLeviCompositionLocalProducts` proves
closedness of `V` and `W` by intersecting the closed radicals. Its first and
second local product lemmas use `SplitsAlong.second`, which reverses the original
splitting order by inversion, to obtain
`K ∩ U₁ = (K ∩ U₀ ∩ U₁)(K ∩ V)` and
`K ∩ U₂ = (K ∩ U₁ ∩ U₂)(K ∩ W)`. For the middle identity, decompose
`x ∈ K ∩ U₁ ∩ U₂` as `a v` by the first splitting. The factorization supplies
`V ≤ U₂`, hence `a = x v⁻¹ ∈ U₂`. This gives
`K ∩ U₁ ∩ U₂ = (K ∩ U₀ ∩ U₂)(K ∩ V)`. Membership in each compact-open carrier is
membership in the same original `K`. The distance condition enters through the
supplied factorization, including its complement inclusions.

## Composite quotient measure

The private `radicalCover` uses the published compact-open subgroup covering of
a dynamic radical. `closedSubgroupCover` pulls that cover back along the closed
embedding of a closed subgroup into a radical. These covers supply right
invariance for the nested intersection kernel and the two complements.

In `composite_measurePreserving`, closedness gives local compactness for the
radicals, intersections, and complements. Second countability of the local field
and its finite-type rational-point space descends to the subgroup carriers.
The product spaces are pseudometrizable and sigma compact, and their source
Haar product measures are locally finite, which supplies regularity.
All measurable structures used here are the Borel structures of the published
objects.

The lemma applies `D.measurePreserving_normalizedProducts` to the middle and
second local product identities, using the intrinsic source Haar measures and
the compatible nested and second quotient measures. It then rewrites by
`intersectionKernelMeasure_source`, `intersectionNormalizedFactor_source`, and
`secondNormalizedFactor_source`. Since every compact-open volume comes from
one `K`, these identities eliminate the normalization scalars. This gives the
exact measure-preserving product homeomorphism
`(U₀ ∩ U₂) × (V × W) → U₂` with the original source Haar measures.
`pairQuotientMeasure_isCompatible` and
`IsCompatible.measurePreserving_factorQuotientHomeomorph` descend this identity
to `D.quotientCoordinates.composite : V × W ≃ᵐ (U₀ ∩ U₂) \ U₂`.
Its source measure is the product of the source-normalized Haar measures on
`V` and `W`; its target is the actual `pairQuotientMeasure K hK ψ₀ ψ₂`.

## Ordered convergence and equality

For the given twist `B` of `A`, the three applications of `pairFamily_spec`
give integral witnesses for the first family at `f`, the second family at that
first value, and the direct family at `f`. For every ambient argument `g` and
every smooth functional on `B`, the direct witness includes absolute scalar
integrability. The composite chart just proved preserves measure, so
`MeasurePreserving.integrable_comp_of_integrable` pulls this integrability back
to `V × W`. The literal composite-coordinate formula and `integrand_mk` identify
the pulled-back integrand with `ℓ(f(v w g))`. This is exactly
`OrderedScalarIntegrable`; no separate product-convergence assumption is added.

`DynamicSource.comp_hasIntegral` now uses the supplied factorization, all three
local products, the two consecutive integral witnesses, and ordered scalar
integrability. It gives a direct quotient integral witness whose value is the
evaluation of the composed operator. The direct `pairFamily_spec` is another
witness for the same integrand and measure. At every `g`,
`SmoothWeakIntegral.HasIntegral.unique`, with the published compact-cofinal
subgroups of the closed common Levi and smoothness of `B`, identifies their
representing vectors. Function extensionality and the two subtype
extensionality steps identify the induced vectors themselves.

The Lean proof uses only the standard axioms `propext`, `Classical.choice`, and
`Quot.sound`.
