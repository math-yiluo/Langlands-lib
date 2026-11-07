# Conditional symmetry of actual standard-intertwiner scalars

Author: Worker 200.

## Provenance and status

`ConditionalStandardInductionScalarSymmetryStatement` is a derived internal
target extending the published `StandardInductionCanonicalScalar`
interface. It states equality of the two canonical rational scalars obtained
by exchanging the two directions of the actual standard-intertwiner
composition, with the subgroup, inducing, compact-model and measure data
fixed. It makes no additional translation claim about the original
literature. This pair defines a proposition; it does not prove it.

The target records the exact conclusion needed from the following algebraic
argument. If two maps have scalar composites in both orders on nonzero
complex vector spaces, their scalars agree: use associativity at a vector
with nonzero image, or show both scalars vanish when one map is zero.
The published generic induced-irreducibility scalarity result can supply
the scalar equations in each order. The published rational uniqueness
construction can then identify the fractions on the common regular
region. A focused proof must implement this argument and establish the
target; this explanation is its provenance rationale, not proof evidence.

## Quantification and objects

The proposition universally quantifies a nonarchimedean local field
`F : Type u` of arbitrary characteristic, a group scheme `L` over `F`,
a topology on its actual rational points, continuity `hp` of
`rationalValuationImageProjection L`, and connected reductivity `hL`.
The canonical rational scalars take values in the existing
`rationalUnramifiedFunctionField L hp hL`, built from the full rational
norm-character family and its actual unramified character space.

The ambient topological group `G : Type uG` is locally compact,
Hausdorff, nonarchimedean and separable. The inducing representation
`A : SmoothRep.{0,uG,uV} ℂ M` uses the canonical smooth representation
framework. The field, ambient group and inducing-carrier universes are
independent. No split, quasisplit or characteristic-zero restriction
is imposed on the reductive group.

The target quantifies semidirect decompositions `P₀ = M U₀` and
`P₁ = M U₁`, closed parabolics and radicals, continuous semidirect
projections, both `IsUnimodularModulus` hypotheses and a common compact
open subgroup `K` with `G = P₀ K = P₁ K`. A topological group isomorphism
`e : L(F) ≃ₜ* M` transports every actual rational norm character to
`M`; continuity of every such character is explicit. These data are
not claimed to have been realized for every reductive rational-point
group.

Both radicals, both subgroup intersections and both quotient spaces
carry their displayed Borel structures. The radical and intersection
measures are regular right-invariant Haar measures. The quotient
measures satisfy the displayed `QuotientIntegration.IsCompatible`
hypotheses. Closedness of `M` and both
`SquaredModulusCompatibility` identities are also explicit.

## Convergence, continuation and irreducibility premises

The original families are the actual
`standardInductionIntertwinerFamily` in the two directions for the
specified measures. Their domains are exactly the corresponding
`standardIntertwiningFullDomainRegion`: scalar absolute convergence
against every smooth-dual functional together with representability
in the original inducing carrier at every vector and group element.

The data `p,q` are `RationalOperatorContinuationData` for the compact
restrictions of those actual families. Their denominators are nonzero
on their entire original full domains. Separate nonempty ambient open
sets `D₁₀,D₀₁` lie inside the respective full domains. The proposition
requires neither domain itself to be open nor the two domains or
convergence sets to intersect.

There are also two independent nonempty ambient open sets `D₀,D₁`.
For every parameter in `Dᵢ`, the actual transported
`UnramifiedLeviInduction` from `Pᵢ` is irreducible. Neither set is
required to lie in a convergence domain. Irreducibility is not assumed
at every regular evaluation parameter or for all tempered inductions.
All four openness assumptions and the irreducibility hypotheses are
explicitly quantified in the proposition.

## Exact equality and limits

The conclusion compares
`standardInductionCompositeCanonicalRationalScalar` with data in the
order `(P₀,P₁,p,q)` against the same construction with order
`(P₁,P₀,q,p)`, exchanging the two radical, intersection and quotient
measures and compatibility proofs accordingly. Each side uses the
published internally chosen normalized coefficient on its own compact
carrier, selected using its own nonempty irreducibility locus. No
vector, linear functional or nonzero-intertwiner hypothesis is added
to the target.

The target allows either intertwiner and either scalar to vanish.
It concerns exchange of the two directions for fixed data; it states
no independence from other parabolic pairs, compact models, measures
or inducing representatives. It imposes and constructs no opposite
relation between the two parabolics. It supplies no value at a pole,
positivity, nonvanishing, source-normalized `j` or `mu`, or Plancherel
formula.

Initial full convergence, whole-operator rational continuation, generic
induced irreducibility and structural realization remain application
obligations. The representation and analysis premises are not permitted
external structural assumptions for completion of the standing
Plancherel program.
