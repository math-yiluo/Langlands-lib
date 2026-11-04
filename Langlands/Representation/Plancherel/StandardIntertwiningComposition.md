# Ordered quotient coordinates and actual standard-integral composition

This is a derived adapter for the standard integral, motivated by Waldspurger,
*La formule de Plancherel pour les groupes p-adiques (d'après Harish-Chandra)*,
IV.1, printed p.279 / PDF p.45, and IV.1(12), printed p.283 / PDF p.49.
It is not a proof of the root-distance composition theorem or rational continuation.

For three radicals `U₀`, `U₁`, `U₂` and actual subgroups `V`, `W` of the ambient
group, `OrderedQuotientCoordinates` records measurable equivalences from `V`
and `W` to the two successive actual left quotients, and from `V × W` to the
direct left quotient. Each equivalence is required to be the actual coset map.
The last uses ordered multiplication `v * w`. The first subgroup lies in both
`U₁` and `U₂`, and the second lies in `U₂`. No commutativity, normality, quotient
group structure or multiplicative equivalence from a direct product is required.
This record does not construct the charts in reductive groups.

For supplied measures on `V`, `W`, and the three quotients, each chart must be
measure preserving; thus the direct quotient measure is exactly the pushforward
of the product measure, with no unspecified scalar. The factor measures are
S-finite. `OrderedScalarIntegrable` requires genuine product absolute convergence
after every smooth functional on the original inducing representation and at every
ambient argument. It does not assert existence of any representing vector.

`HasIntegral.comp_ordered` starts with an actual normalized induced vector `f`,
an intermediate normalized induced vector `F`, and the two standard-integral
relations representing the first integral by `F` and the second by a function `J`
in the original inducing carrier. It transports the first relation to `V` at
`w * g`, transports the second relation to `W`, and applies scalar weak Fubini.
The coset formulas identify its product integrand with `f((v * w) * g)`;
transport through the product chart gives the direct standard-integral relation.
`mem_domain_comp_ordered` derives the direct domain membership from this relation.
`operator_eq_comp_ordered` then uses smooth-dual separation to identify the
selected direct integral with `J`.

`targetOperator_mem_domain_comp_ordered` specializes the intermediate vector
to the existing target-valued standard integral. Its premises require that
this actual vector belongs to the outer integral's actual domain and that the
original input has the stated scalar product convergence.
`operator_comp_targetOperator_ordered` then equates the selected direct integral
on the derived domain with the selected outer integral of that intermediate
vector, as actual functions on the ambient group.

`domain_eq_top_comp_ordered` proves that the direct domain is the whole source
if both successive domains are full and every source input satisfies the product
absolute convergence condition. It uses the first target operator, whose target
covariance requires the explicit compatible Haar measures and squared-modulus
identity from `StandardIntertwiningTarget`. No corresponding direct full-domain
conclusion is assumed.

`fullSourceIntertwiner_comp_ordered` uses that derived direct full domain and
proves equality of the direct ambient intertwining map with the composition
of the two actual full-source standard intertwiners. All three are the published
integral constructions, rather than arbitrary maps satisfying an assumed
composition equation. It uses a third semidirect decomposition for the final
target, compatible Haar measures on all three quotients, and all three
squared-modulus comparisons. Equality of underlying functions, proved by
`operator_eq_comp_ordered` and the standard-integral specifications, gives equality
of the actual induced vectors and then of the intertwining maps.

The ambient group and carrier universes are independent. The source and
intermediate inductions use the canonical `SmoothRep` and existing positive
Levi-normalized induction, with a common actual Levi. Their semidirect
decompositions and closed radicals are explicit. The selected-integral comparison
also requires the Levi to be closed, supplying compact-open cofinality for
uniqueness. The target-operator specializations also assume the ambient group is
Hausdorff and the supplied subgroup and quotient measurable spaces are their
Borel spaces, with regular two-sided Haar measures as required by the existing
target construction. The two quotient measures with target radical `U₂` share
one supplied Haar measure on `U₂`, and have separate intersection Haar measures.
No topology, norm, completion or bidual is installed on the carrier.

The existence of actual complementary-root charts under root-distance additivity,
their measurable properties and exact Haar normalization, and the required product
convergence remain application obligations. They may not be installed as permanent
structural assumptions of the Plancherel program. The squared-modulus premises
and full domains of the two successive integrals also remain obligations for
the actual reductive application. Rational extension and equality of continued
families require their separate prerequisites. This adapter alone closes none of
the whole-program completion conditions.
