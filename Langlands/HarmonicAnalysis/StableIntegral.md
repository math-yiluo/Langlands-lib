# Scalar integration by compact open stabilization

This internal foundation isolates the scalar stabilization used in Shahidi,
*Fourier transforms of intertwining operators and Plancherel measures for
GL(n)* (1984), printed page 78, the discussion following (1.1).
The registered source is `shahidi-1984-fourier`, SHA256
`a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`.
Shahidi decomposes an induced vector into a compactly supported part and a
remainder whose scalar integrals vanish over every sufficiently large compact
open subgroup. The present general construction records the resulting meaning
of stabilization. It does not prove that decomposition or apply it to induced
vectors.

All declarations are in `Langlands.HarmonicAnalysis`. The domain `X` is a
topological additive commutative group equipped with a measurable space, and
`μ` is an actual measure on `X`. No Haar or normalization hypothesis is needed
for the construction. Rectangular matrix additive groups are the intended
application; the identification with Shahidi's integration subgroup is a
separate obligation.

`HasStableIntegral μ f z` means that there is a compact open additive subgroup
`K` such that, for every compact open additive subgroup `L` containing `K`,
the scalar function `f : X → ℂ` is integrable on `L` and its integral on `L`
equals `z`. In particular integrability is required at the threshold itself.
Including integrability prevents the totalized Bochner integral from assigning
spurious stabilization to divergent truncations.

`isCompact_sup_openAddSubgroup` proves that two thresholds have a common
compact open upper bound. In an abelian group the carrier of their subgroup
supremum is their pointwise sum. Addition is continuous, so the sum of the
two compact carriers is compact. Openness is supplied by the open subgroup
lattice.

`HasStableIntegral.unique` evaluates two proposed stable values at the
supremum of their thresholds. `HasStableIntegral.add` uses the same supremum,
then integrability and additivity of scalar integration on every larger
compact open subgroup. `HasStableIntegral.smul` preserves the threshold and
uses homogeneity of the scalar integral. `HasStableIntegral.zero` explicitly
requires that at least one compact open additive subgroup exists.
`HasStableIntegral.congr` transports stabilization along pointwise equality.

`stableIntegrableSubmodule μ hX` consists exactly of the actual scalar functions
with some stabilized value. Its parameter `hX` proves existence of one compact
open subgroup, needed to include the zero function. Closure follows from the
preceding addition and scalar multiplication proofs.
`stableIntegral μ hX` is the complex linear map from that submodule to `ℂ`.
It chooses a value only from each function's proof of existence; uniqueness
proves the linear map laws.
`hasStableIntegral_stableIntegral` verifies the chosen value, and
`stableIntegral_eq` identifies it with any value satisfying the relation.

This unit asserts neither stabilization for arbitrary functions nor absolute
integrability on the whole group. It supplies no Jacquet functional,
intertwining operator, rational continuation, or local coefficient.
