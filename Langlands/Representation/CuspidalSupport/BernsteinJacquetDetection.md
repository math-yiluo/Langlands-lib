# Actual cuspidal Jacquet detection and orthogonality

Worker 137 derives this internal construction and its consequences from the published
`RationalMinimalJacquetArbitraryCarrier` minimum-cardinality argument,
irreducible-subquotient existence, exact Jacquet restriction and canonical
standard-Levi transport. It preserves independent field and representation
carrier universes. These are internal supporting results for the actual
condition (iii) of `BernsteinBlockCharacterizationStatement`; no separate
original-literature translation is claimed.

`exists_bernsteinCuspidalDatum_jacquet_subquotient` constructs a genuine
`BernsteinCuspidalDatum` occurring in a standard normalized Jacquet module of
each nonzero smooth representation. `bernsteinNonzeroJacquetDatum` chooses
such a datum and retains its actual subquotient witness.

The standard-family structural hypotheses supply connected reductivity,
a maximal split torus, a generic cocharacter and closed standard Levis and
radicals. Published structural proofs supply the standard-cocharacter,
Levi-intersection and relative-root-system facts. Minimal nonzero Jacquet
restriction is cuspidal inside its Levi. Choose an irreducible subquotient in
the same carrier universe; exactness of the proper inner Jacquet functors
preserves cuspidality. Pull it back along the canonical standard-Levi
homeomorphism to obtain the scheme-side representation of the datum.
The inverse pullback is actually isomorphic to the original representation,
so it retains both cuspidality and occurrence in the original Jacquet module.

`subsingleton_iff_no_bernsteinCuspidalDatum_jacquet_subquotient` identifies
vanishing of the original object with absence of all these actual cuspidal
occurrences. For a zero source, the surjective coinvariant quotient has
subsingleton carrier. Any actual subquotient therefore has subsingleton
carrier, which contradicts irreducibility of a datum. Conversely, a
nonzero source has an occurrence by the detection theorem.

At the saturated carrier universe `max uF uV` used by the characterization,
`subsingleton_of_bernsteinJacquetExclusion_of_not_inertiaRelated` proves that
an object satisfying `BernsteinJacquetExclusion` for two unrelated actual
data must vanish. Any detected datum would have to be related to both
data; symmetry and transitivity would then relate the prohibited pair.
Thus this consequence needs no induction-support comparison.

`no_common_irreducibleSubquotient_of_bernsteinJacquetExclusion` uses the
published closure of condition (iii) under actual subquotients to exclude
a common irreducible subquotient of objects satisfying condition (iii)
for unrelated data. Finally,
`hom_eq_zero_of_bernsteinJacquetExclusion_of_not_inertiaRelated` applies the
published general Hom-vanishing theorem: a nonzero morphism would have a
nonzero image, hence an irreducible subquotient common to its source and
target. There is no finite-length, admissibility, category decomposition
or support-uniqueness premise.

This construction does not prove cuspidal induction support, the
induction/Jacquet support comparison, a fixed-Levi embedding or geometric
exclusion for induced inertia-block objects. The unconditional Bernstein
block characterization remains open. In particular, these orthogonality
results concern condition-(iii) classes; identifying them with the original
Bernstein blocks still requires the missing characterization inputs.

The instances introduced here have explicit names specific to this module so that
combined imports retain distinct declarations. Their types, bodies and instance
scopes are unchanged.
