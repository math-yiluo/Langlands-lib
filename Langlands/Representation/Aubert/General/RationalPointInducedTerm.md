# Induced geometric terms from point-source intersection identities

This internal adapter uses `PointSourceIntersectionIdentities` for an actual
point Weyl Coxeter system. It retains every standard subset, minimum double
coset representative and normalizer lift. The fine indices are the canonical
`intersectionLeviIndex` subtypes in the original coarse labels.

`pointSourceIntersectionIndex` identifies their ambient labels with the literal
simple-image intersections. The final extensionality step reconciles the
finite-set membership decisions. `pointSourceIntersectionConjugationMembership`
rewrites the fine source and target Levis using the structural identities and
then applies `geometricIntersectionMembership`. Its direction is
`x ↦ n⁻¹ * x * n`, from the target fine Levi to the source fine Levi. No separate
standard Levi-conjugation law or root-sign comparison is needed by this adapter.

`geometricTermK0_eq_standard_of_pointSource` applies
`geometricTermK0_eq_standardOfEq` after rewriting the source and target subgroup
identities at those indices. It identifies the actual geometric term with its
literal standard restricted term. The actual decomposition and preservation
witnesses may be arbitrary. Source Jacquet and target induction preservation
for the standard term are taken from the displayed literal restricted
`ParabolicFiniteLength` hypotheses.

`pointSourceInducedGeometricTermK0` composes ambient normalized induction at I
with the actual geometric term from the Levi at J. Its geometric-factor
preservation is derived by `geometricTermFiniteLength_of_pointSource`, using
the structural identities and the supplied restricted preservation. Source
and target actual decomposition witnesses remain explicit and arbitrary;
`geometricIntersectionDecompositions_of_pointSource` supplies them when needed.

`pointSourceInducedGeometricTermK0_eq` identifies this complete induced map
with `inducedLeviAlternatingTerm` at `intersectionLeviIndex cs I J w`.
The proof first constructs `standardInductionStagesIso` at both fine indices.
It then applies `inducedStandardIntersectionTermK0_eq`: target stages replace
the first two inductions by direct fine induction, the explicitly supplied
fine-Levi induced Weyl equation removes conjugation after induction, and source
stages in reverse produce the literal source induction/Jacquet composite.
Finally the geometric-to-standard comparison identifies the original map.
These are equalities on the full integer-linear exact finite-length K0,
including all short exact sequence relations and virtual classes.

The topological statements use canonical `pointTopology`, a locally compact
nonarchimedean point group, closed ambient Levis and radicals, the standard
Levi intersection statement, connected reductivity, a maximal split torus,
and a generic cocharacter. Ambient and literal restricted
`ParabolicFiniteLength` are displayed inputs; the existing
`standardParabolicFiniteLength` and `standardLeviParabolicFiniteLength`
adapters derive these from the final target's preservation and topological
premises. The stages equality also retains a nonarchimedean local field,
`StandardCocharacterStatement`, continuous ambient projections and ambient
and restricted compact-subgroup-limit conditions. Universes u and v remain
independent, and representation carriers have universe `max (u + 1) v`.

The provenance is internal composition of the named intersection, subgroup
comparison, normalized induction stages and exact-K0 functoriality results.
The stages construction derives its Haar-modulus product through
`standardJacquetModulus_stages`. The comparison and K0 descent use actual
functor isomorphisms, composition and subgroup pullback; they do not invoke
Langlands classification, character independence, the geometric lemma,
adjointness or a cuspidal-support theorem. Subgroup pullback's finite-length
proof uses an invariant-subspace order isomorphism, including the helper
`CuspidalSupport.JacquetLength.compSubrepresentationOrderIso`; that helper is
an elementary transport result, not a cuspidal-support theorem.

The structural source identities and fine-Levi induced Weyl equation remain
explicit inputs here. Their existence, the actual Coxeter/root comparisons,
geometric expansion, signed assembly and the exact final rational Aubert
compatibility proposition remain separate obligations. This adapter asserts
no scheme Coxeter realization or extra premise for that final proposition.
