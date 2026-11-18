# Levi Iwasawa weights with an arbitrary compact source subgroup

This internal module removes the restriction that the source compact factor
used to define the Levi Iwasawa weight be the literal intersection of the
original ambient compact subgroup with the Levi. It derives a pointwise
comparison from the published `LeviData` identities and positivity on a
compact set. It introduces no original-literature assertion and proves no
averaged Xi or orbit-coefficient estimate.

Let `G = P0 K`, and let `LeviData` describe `P = M U`, its displayed projection,
the original positive character `delta0`, the Levi character `delta0M` and the
relative character `deltaP`. Let `KM` be a subgroup of `M` with
`M = (P0 in M) KM`. Assume the original `delta0` is one on `P0` intersect `K`,
and that `deltaP` is one on `KM`.

`LeviData.iwasawaWeight_mul_arbitraryCompact` gives an exact factorization
for every `p` in `P` and `kM` in `KM`. The original ambient weight at `kM p`
is the product of the square root of `deltaP` at the original Levi projection,
the source Levi weight at `kM` times that projection, and the original
ambient weight at an actual source-Iwasawa compact factor `kprime` in `KM`.
The compact factor is supplied existentially, with its membership proved.
No hypothesis puts `kprime` in the original `K`, so its weight is retained.

The implementation follows the existing elementary factorization in
`SphericalLevi`: write `kM m = a kprime` in the source Levi, and form the
kernel element `v = kprime m^{-1} p kprime^{-1}`. Then `kM p = (a v) kprime`.
The kernel lies in `P0`, its `delta0` is one, and the character relation gives
`delta0(a) = deltaP(m) delta0M(a)` because `deltaP` is one on both displayed
source compact factors. The original left-`P0` weight equivariance evaluates
the product and preserves the final ambient weight at `kprime`.

For a topological ambient group, an open original `K`, and compact `KM`,
`exists_sourceLeviWeight_lower` proves that the original ambient weight has a
uniform positive lower bound on all points of `KM`. The original weight is
continuous by the published local-constancy result and is positive everywhere.
Its restriction to the compact source subgroup attains a positive minimum.
`sourceLeviWeightLowerConstant` chooses such a bound before all varying
parabolic points, and its `_spec` theorem states positivity and the uniform
lower inequality.

`LeviData.iwasawaWeight_le_mul_arbitraryCompact` combines these facts. The
product of the relative square-root character and source Levi weight is
bounded by the reciprocal of the chosen positive constant times the original
ambient weight at `kM p`, uniformly in `p` and `kM`. It keeps the original
ambient `K`, original Iwasawa weight, original Levi projection and arbitrary
displayed source compact subgroup. The compact source subgroup is not
identified with the original literal Levi intersection.

The character-triviality premise on the arbitrary source subgroup remains
explicit in this generic comparison. Its actual rational-point proof, double
averaging, the compact translation bound for Xi, and the adapter for the
original orbit coefficient are separate steps. Neither an equality of Xi
functions nor full wave-packet Schwartz membership or continuity is claimed.
