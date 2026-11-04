# Countable topology for standard-intertwining composition

This internal construction discharges topological measure assumptions in the
conditional actual-integral composition adapter. The motivating source is
Waldspurger (2003), registered as `waldspurger-2003-plancherel`, IV.1,
printed p.279 / PDF p.45: its complementary-unipotent factorization gives an
ordered iterated integral. The rational composition identity IV.1(12),
printed p.283 / PDF p.49, is a later application, whose geometric and
continuation obligations are not proved here.

Keep the preceding notation: `I₁₀ = U₀.subgroupOf U₁`,
`I₂₁ = U₁.subgroupOf U₂`,
`H = (U₀.subgroupOf U₂).subgroupOf I₂₁`,
`K = (V.subgroupOf U₂).subgroupOf I₂₁`, and `L = W.subgroupOf U₂`.
These are actual subgroup carriers with their induced topologies. Their
Haar measures are independently supplied; no restriction of ambient Haar
measure is taken.

`firstComplementLocallyCompactSpace` constructs local compactness of `V`
from local compactness of `G`, closedness of `U₁`, and the supplied literal
homeomorphism `D.first : I₁₀ × V ≃ₜ U₁`.
Closedness first makes `U₁` locally compact; the homeomorphism transfers
local compactness to the product; its open surjective second projection
then gives local compactness of `V`. The first factor is nonempty because
it is a subgroup. `secondComplementLocallyCompactSpace` uses the same
argument with `D.second : I₂₁ × W ≃ₜ U₂` and closedness of `U₂`.
Neither construction requires an additional closedness premise on `V`
or `W`.

`comp_hasIntegral_of_secondCountable` applies
`comp_hasIntegral_of_seedRegularity` under explicit
`SecondCountableTopology G`, deriving every individual regularity,
S-finiteness and product Borel premise of that adapter, including regularity
of its four genuine seed products
`μH.prod μK`, `μI₂₁.prod μL`, `μI₁₀.prod μK`, and `μK.prod μL`.
Those properties are conclusions of typeclass synthesis inside the proof,
not additional parameters of this theorem.

The implemented proof obtains local compactness of `U₁`, `U₂`, `I₂₁`,
`I₁₀` and `H` from the closedness of the relevant `Uᵢ`; the nested
closedness assertions are preimages under continuous subtype inclusions.
It installs the two complement constructions above and transfers their
local compactness to `K` and `L` through the existing canonical continuous
group equivalences. The local helper `subgroupSecondCountable` explicitly
uses Mathlib's subtype second-countability instance for all the nested
subgroups.

On these carriers, Mathlib supplies regularity of topological groups and
second countability, hence pseudometrizability by Urysohn's theorem.
Separable locally compact groups are sigma compact. Haar measures are
finite on compact sets and therefore locally finite; second countability
also gives sigma-finiteness, hence S-finiteness. Products are locally finite
using S-finiteness of the second factor, and their sigma compactness and
pseudometrizability give regularity by
`Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure`.
`Prod.borelSpace` supplies the product Borel structures. The proof finally
calls the preceding seed-regularity adapter with the same measures,
normalizations and integral witnesses.

The theorem retains individual Borel measurable structures; the
nonarchimedean, Hausdorff and locally compact ambient group; closedness of
all three `Uᵢ`; the three literal charts in `D`; independent Haar measures
and the displayed right-invariance assumptions; four compatible Weil
measures; the three local compact-open product identities; compactness of
`R`, `S`, `B`, `T`, `C`; and the four genuine unit-mass identities for
`R`, its `I₁₀` part, `S`, and its `H` part. The first normalized factor
and second normalized factor are exactly those of the imported modules.

Both actual `HasIntegral` witnesses, the actual intermediate induced
section, and `OrderedScalarIntegrable` remain hypotheses. The latter
tests absolute scalar integrability against every smooth functional on
the original carrier. The conclusion is the direct `HasIntegral`
relation for the same endpoint quotient measure and the same function
`J`. The representation is the canonical `SmoothRep` on the common Levi;
the group and representation-carrier universes are independent.

The ambient countability premise is explicit. For actual finite-type
affine group-scheme points, the published
`Langlands.GroupScheme.affinePointsSecondCountableTopology` and
`affinePointsLocallyCompactSpace` provide the corresponding properties
under their coefficient-space assumptions. This module does not construct
an adapter to every reductive rational-point family or discharge those
coefficient assumptions.

The construction uses general topology and measure theory from the pinned
Mathlib with the previously defined subgroup charts. It does not prove
arbitrary convergence, original-carrier representability, existence of the
charts or compatible normalizations, rational continuation, or a full
Plancherel result. In particular it assumes no irreducibility of parabolic
induction and closes no whole-task completion condition.
