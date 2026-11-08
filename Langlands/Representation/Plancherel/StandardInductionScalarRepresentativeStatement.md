# Conditional representative independence of actual canonical scalars

Author: Worker 200.

## Provenance and status

`Langlands.Plancherel.ConditionalStandardInductionScalarRepresentativeStatement`
is an internal derived target extending the published
`StandardInductionCanonicalScalar` interface. It compares the canonical
rational scalar of the actual two-direction standard-integral composite
for two equivalent inducing representations, allowing independent rational
continuations and coefficient-selection loci. This pair defines a
proposition and supplies no proof of it. It makes no additional
translation claim about an original numbered literature assertion.

The proposed proof route specializes the published
`continuedInductionCompositeRationalScalar_representative_independent`
theorem to the actual `standardInductionIntertwinerFamily` in each
direction. The original comparison squares must be derived from
`fullSourceIntertwiner_natural`, with full-domain equality derived from
`domain_eq_top_iff_equiv` and `twistEquiv`. They are not premises of the
new target. The generic theorem derives scalarity from actual induced
irreducibility of the first representative. Specializing its normalized
coefficients to the internally chosen coefficients on both compact
carriers gives the asserted canonical equality. This explains the
internal provenance and intended use; it is not accepted proof evidence.

## Fixed actual data

The proposition universally quantifies a nonarchimedean local field
`F : Type u` of arbitrary characteristic, a group scheme `L` over `F`,
a topology on its actual rational points, continuity `hp` of
`rationalValuationImageProjection L`, and connected reductivity `hL`.
Both scalars belong to the existing
`rationalUnramifiedFunctionField L hp hL`, on the full rational
norm-character family of `L`.

The ambient group `G : Type uG` is locally compact, Hausdorff,
nonarchimedean and separable. The data include semidirect decompositions
`P₀ = M U₀` and `P₁ = M U₁`, closed parabolics and radicals, the two
`IsUnimodularModulus` hypotheses, continuous semidirect projections,
and a common compact open subgroup `K` with `G = P₀ K = P₁ K`.
A topological group isomorphism `e : L(F) ≃ₜ* M` transports the actual
rational norm characters to the literal Levi subgroup `M`;
continuity of every such character is explicit.

Both radicals, their subgroup intersections and their left quotient
spaces carry the displayed Borel structures. Their radical and
intersection measures are regular right-invariant Haar measures.
The quotient measures `q₁₀,q₀₁` satisfy the respective
`QuotientIntegration.IsCompatible` hypotheses. Closedness of `M` and
both `SquaredModulusCompatibility` identities are explicit. All these
subgroups, measures, normalizations and compact-model data are shared
between the two sides of the equality. Their realization for an arbitrary
reductive rational-point group is not claimed by this target.

## Representatives, continuations and loci

The two inducing objects are canonical
`A : SmoothRep.{0,uG,uV} ℂ M` and
`B : SmoothRep.{0,uG,uW} ℂ M`, with an equivariant linear equivalence
`φ : A.representation.Equiv B.representation`. The field, ambient-group
and two inducing-carrier universes are independent. No finite dimension,
splitness, quasisplitness or characteristic-zero assumption is imposed.

The four continuation data `pA,qA,pB,qB` are independently supplied
`RationalOperatorContinuationData` for the compact restrictions of the
actual `standardInductionIntertwinerFamily`, in both directions and for
both representatives. Their original regions are the respective
`standardIntertwiningFullDomainRegion`. Such a region requires scalar
absolute convergence against every smooth-dual functional and
representability in the original inducing carrier for every source
vector and group element. It is not just a scalar convergence domain.
Each continuation uses a single denominator for its whole operator
family, nonzero throughout that family's original full domain.

Each of `DA₁₀,DA₀₁,DB₁₀,DB₀₁` is a separately chosen nonempty
ambient open subset of the corresponding full domain. These four sets
need not coincide or intersect. Full-domain openness is not assumed.
The target does not require that the B continuations are constructed by
conjugating the A continuations, or that any denominators agree.

There is a separate nonempty ambient open locus `DA` on which the actual
`P₀`-induction of `A` is irreducible. A separately chosen nonempty locus
`DB` has irreducible actual `P₀`-inductions of `B`; `DB` need not be open.
No irreducibility locus must lie in a convergence domain. The second
locus supplies the nonzero compact carrier and the internally selected
normalized coefficient in B's canonical definition. Generic scalarity
is needed only for the first representative. No scalarity or original
comparison-square hypothesis is present in the proposition.

## Exact conclusion and retained obligations

The conclusion is equality of the two
`standardInductionCompositeCanonicalRationalScalar` values, using the
same ordered subgroup, compact-model and measure data. The A side uses
`pA,qA`, its own convergence witnesses and `DA,hiA`; the B side uses
`pB,qB`, its own convergence witnesses and `DB,hiB`. Each canonical
scalar uses its internally chosen normalized compact coefficient.
No vector, functional or nonzero-intertwiner hypothesis is supplied.
Although the generic comparison proof may use transported A convergence
sets for B, the conclusion retains B's independently chosen witnesses;
the canonical definitions depend on those convergence witnesses only
through proofs of nonemptiness of the full domains.

Initial full convergence, whole-operator rational continuation, generic
actual induced irreducibility and realization of the displayed structural
data remain application obligations. The representation and analysis
premises are not permitted external structural inputs for completion of
the standing Plancherel program.

The target permits zero operators and zero scalars. It supplies no value
at a pole, nonvanishing, positivity, parabolic-pair independence,
compact-model or measure independence, opposite relation, source-normalized
`j` or `mu`, or Plancherel theorem. It concerns inducing-representative
independence for the fixed actual data only.
