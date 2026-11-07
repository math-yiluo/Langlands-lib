# Ordered unramified spherical generation

The theorem
`Langlands.Correspondence.orderedUnramifiedSphericalGeneration` proves the
unchanged proposition
`Langlands.Correspondence.OrderedUnramifiedSphericalGenerationStatement.{uF} F`
from `Langlands/Correspondence/SphericalStandardModulePrerequisites.lean`.
For every prime, every p-adic field `F`, every positive rank `r + 1` and every
tuple `z : Fin (r + 1) → ℂˣ` with weakly increasing complex norms, any
subrepresentation of the actual normalized upper-Borel principal series
`principalSeriesOfTuple F z` with a nonzero spherical fixed vector is the whole
principal series. Repeated parameters and distinct parameters of equal norm
are allowed. The field universe is arbitrary. There is no irreducibility,
unitarity, regularity, strict-order or spherical-head premise.

This is an internal derivation from published Library results. It proves the
generation assertion of Matringe (2013), Corollary 1.2, using actual tempered
realization, an independently constructed spherical quotient, and the
finite-length fixed-line criterion. It does not follow the source's string
regrouping argument.

The auxiliary theorem
`eq_top_of_temperedRealization_sphericalQuotient` takes an actual equivalence
from a tempered standard module to the principal series and an actual
irreducible spherical quotient of that series. The tempered datum already has
strictly decreasing exponents between its blocks, so
`glRegularLanglandsHeadExistence` supplies a strong irreducible head of its
standard module. The block product has finite length by
`RegularHeadExistence.standardModule_finiteLength_of_productPreservation` and
`admissibleFiniteLengthProductPreservation`. Transport along the actual
equivalence gives a strong head and finite length for the principal series.

The private lemma `head_of_head_quotient` then shows that the supplied
irreducible quotient is itself a strong head: every irreducible quotient map
has the same kernel as the original head map, so it also has the same kernel
as this quotient map. No sphericality conclusion is inferred from kernel
uniqueness alone; the supplied quotient already has a nonzero spherical fixed
space.

Apply `SphericalGeneration.eq_top_of_finiteLength_spherical_head` to this
strong spherical head. The actual spherical subgroup is compact and open.
`SphericalGeneration.scalarEvaluation_injective` bounds its fixed space in the
principal series by one dimension through evaluation at the identity.
Compact fixed-vector lifting makes the head map nonzero on that fixed space;
the dimension bound makes its restriction injective. Finite length supplies a
coatomic subrepresentation lattice. If the given subrepresentation were proper,
it would lie in a maximal proper subrepresentation. The corresponding
irreducible quotient has the same kernel as the strong head map. The nonzero
fixed vector would therefore be killed by the head map, contradicting
injectivity on fixed vectors. The subrepresentation is top.

The theorem `orderedUnramifiedSphericalGeneration_of_temperedRealization`
applies this criterion to each ordered tuple using the published
`exists_spherical_irreducible_quotient`. That construction supplies an actual
surjective intertwiner and a nonzero spherical fixed space. It obtains them
by constructing a spherical irreducible segment product inside the
inverse-parameter principal series and dualizing the embedding. Its weak-order
hypothesis allows repetitions and equal norms.

Finally `orderedUnramifiedSphericalGeneration` supplies the realization
hypothesis with the published `orderedUnramifiedTemperedRealization`, choosing
the block carrier universe to be the field universe. That result groups
equal-norm parameters into irreducible tempered blocks and constructs the
actual standard-module equivalence. All representation carriers used in the
criterion thus lie in the field universe, with no universe restriction on the
field and no extra assumption on the original principal series.
