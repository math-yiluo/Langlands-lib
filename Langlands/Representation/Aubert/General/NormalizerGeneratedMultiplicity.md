# Multiplicity from actual normalizer conjugates

This internal derived construction proves the elementary Hom bound used after
an actual weak-Jacquet decomposition by regular normalizer conjugates has
been supplied. It reuses `NormalizerRegularity` and admissible Schur and
introduces no new external mathematical input.

Let `M` be a subgroup of an arbitrary topological group `G`, let `σ` be an
irreducible regular smooth complex representation of `M`, and let `τ` be
another smooth representation of `M`. The group, `σ` carrier, `τ` carrier and
index universes are independent. Regularity means precisely the published
`IsNormalizerRegular`: a normalizer element outside `M` cannot give an
equivariant equivalence between its inverse-conjugate of `σ` and `σ`.

The data are an intertwiner `i₀ : σ → τ` and intertwiners `iⱼ : gⱼσ → τ`
for a family of actual normalizer elements `gⱼ` outside `M`. The generating
hypothesis says that the linear range of `i₀`, together with the supremum
of the linear ranges of the `iⱼ`, spans all of `τ`. The index family need
not be finite. The supplied maps need not be injective and their ranges
need not form a direct sum. In particular the result applies to a supplied
decomposition with one identity summand and nonidentity normalizer summands,
but it does not construct such a decomposition.

`normalizerGeneratedRestriction` is complex-linear precomposition with
`i₀`, from `Hom_M(τ,σ)` to `End_M(σ)`. Its definition needs none of the
irreducibility, regularity or spanning premises.

To prove injectivity, take maps with equal restrictions and subtract them.
Their difference vanishes on the range of `i₀`. On each other generating
range, its composite with `iⱼ` is an intertwiner `gⱼσ → σ`. The published
`normalizerConjugate_hom_eq_zero` makes this composite zero. The kernel thus
contains every generating range and hence the whole source, so the two maps
are equal. No admissibility or semisimplicity is used in this step.

`normalizerGeneratedHom_rank_le_one` additionally assumes admissibility of
`σ`. The published `admissibleSchur_homEquiv` identifies `End_M(σ)` with
`ℂ`. Composing it with the restriction injection gives a complex-linear
injection from `Hom_M(τ,σ)` into `ℂ`. Mathlib's lifted cardinal-rank
monotonicity and the rank-one value of the scalar field yield rank at most
one, without relating the source and target carrier universes.

This is not the Jacquet decomposition of Waldspurger III.7.3 and is not a
proof of generic irreducibility. A consumer must construct the actual
source and generating maps with the required spanning property, establish
regularity and admissibility of `σ`, and, when `τ` is the weak Jacquet
part, compare it with the actual normalized Jacquet module and induction
model. Those representation-theoretic obligations remain open here. The
separate generic filtration Hom bound can give a different route that does
not require these generating maps; this lemma makes no filtration claim.
