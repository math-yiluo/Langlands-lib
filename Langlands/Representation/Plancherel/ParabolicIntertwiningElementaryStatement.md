# Elementary structural and transport targets for standard intertwining

`Langlands.Plancherel.ParabolicIntertwiningElementaryStatement` is a
Prop-valued internal target grouping three elementary prerequisites of the
published `ConditionalParabolicIntertwiningStatement`. It retains independent
field/group universe `u` and carrier universes `uV,uW`. This module states the
three assertions; it does not prove them or the finite-length theorem.

The provenance is internal and derived. The radical assertion is the
specialization of the published dynamic-radical unimodularity theorem to the
actual radical identified by a compatible root presentation. The two transport
assertions isolate formal consequences of the existing actual integral's
naturality. They introduce no new analytic convergence or rationality claim,
and do not translate an additional numbered result from the literature.
The motivating conditional theorem and its original-source conventions remain
in `ParabolicIntertwiningStatement`.

`SuppliedParabolicRadicalUnimodularityStatement` quantifies over an arbitrary
nonarchimedean local field, an actual connected reductive ambient group scheme,
and its canonical rational-point topology. Local compactness and the
nonarchimedean group structure are explicit. Given the complete compatible
presentation of `p:P→G`, `l:M→P`, and `a:A→M`, a geometric radical `n:U→P`,
and closedness of the actual point image of `n ≫ p`, it asserts triviality
of that image's inner Haar modulus. There is no assumption of splitness,
characteristic zero, or an inducing representation. It assumes the supplied
geometric radical and presentation; it does not assert their general
existence. The expected declaration-level inputs are
`ParabolicRootPresentation.range_comp_radical_eq` and
`Aubert.General.DynamicNormalization.dynamicUnipotent_isUnimodular`.

`StandardIntertwiningFullDomainTransportStatement` works in the existing
general locally compact nonarchimedean subgroup framework. For the same
semidirect decomposition, closed source radical, target radical, and actual
quotient measure, it asserts that two equivariantly equivalent smooth inducing
representations have full domain simultaneously. The carriers have independent
universes. Domain is the actual integral domain: scalar absolute convergence
and a representing vector in the original inducing carrier at every ambient
argument. The expected proof uses
`StandardIntertwining.inducedEquiv_mem_domain_iff`.

`StandardIntertwiningRepresentativeNaturalityStatement` additionally retains
the second actual semidirect decomposition, closed target radical, Borel
structures, compatible regular right invariant Haar measures, closed Levi,
Hausdorff ambient topology, and squared-modulus identity used by the published
target operator. From a full-domain proof for `A` and an equivariant equivalence
from `A` to `B`, it asserts the existence of a full-domain proof for `B` together
with the equality `J(B) ∘ Ind_P(e) = Ind_P'(e) ∘ J(A)`. Both sides use the
existing actual full-source integral. Its formal square can use
`StandardIntertwining.fullSourceIntertwiner_natural` after domain transport.
Initial convergence and squared-modulus compatibility remain premises of this
formal helper, and remain conclusions to prove in the whole conditional
finite-length theorem. This helper does not assert rational continuation.
