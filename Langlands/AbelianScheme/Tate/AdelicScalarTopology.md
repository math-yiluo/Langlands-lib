# Joint continuity of actual adelic Tate scalar actions

This internal construction bundles the already defined full and away adelic
actions on the rational Tate modules of an abelian scheme as continuous maps.
It derives continuity from the actual residue actions on the integral limits,
their open rational charts, and the normalized scalar homeomorphisms in
`RationalScalarTopology`. It does not introduce a new action or a new
comparison existence assertion.

The helper `Langlands.TateScalarExtension.continuous_action` concerns a
commutative ring `R`, an additive commutative group `M` with an `R`-module
structure, topologies on both, and a jointly continuous scalar operation
`R × M → M`. Give their rationalizations the final topologies. Assume that
the integral chart `a ↦ 1 ⊗ a` is an open embedding for both `R` and `M`.
Then the existing algebraic action

\[
(\mathbb Q\otimes_{\mathbb Z}R)\times
(\mathbb Q\otimes_{\mathbb Z}M)\longrightarrow
\mathbb Q\otimes_{\mathbb Z}M
\]

is jointly continuous.

The proof reuses `Langlands.Topology.Rationalization.exists_chart` from
[Lattice](../../Topology/Rationalization/Lattice.md) to write each input as a pure
tensor with nonzero rational first factor. Multiplication by a nonzero rational is
a homeomorphism for the final topology, so each corresponding chart is open.
The product of the two charts is also an open embedding. On this product
chart the action is

\[
(a,x)\longmapsto(qr)\otimes(a\mathbin{\bullet}x).
\]

This is continuous by the integral action and the final-topology chart map.
Continuity on the open chart proves continuity at the chosen point. The
argument uses open embeddings explicitly; it does not infer joint continuity
from separate continuity or from an unrestricted product-of-quotients rule.

The two `isOpenEmbedding_integralChart` theorems, in the full and away
comparison namespaces, establish the scalar hypotheses. They compose the
open integral-adele inclusion with the inverse rational homeomorphism.
Normalization on `1 ⊗ a` identifies this composition with the integral chart.
The full comparison `h`, and the away comparison `hAway` coupled to that same
`h`, remain explicit arguments.

For an actual abelian scheme `A/S` and any test scheme `T` over `S`,
`continuous_finiteAdeleAction` applies the helper with
`R = ProfiniteIntegerRing` and `M = Integral A T (fun _ => True)`.
The vector chart is open by `isOpenEmbedding_full_toRational`, and the
integral action has the previously constructed `ContinuousSMul` instance.
Precomposition with the inverse scalar homeomorphism gives joint continuity
of the existing finite-adelic action. Thus

`finiteAdeleContinuousAction A T h`

is a continuous map from
`FiniteAdeles ℚ × RationalFull A T` to `RationalFull A T`. Its application
lemma identifies it with `finiteAdeleAction A T (fun _ => True) h`.
`finiteAdeleModule_continuousSMul` packages the same fact for the already
defined `finiteAdeleModule`, installed locally.

The away declarations `continuous_primeToFiniteAdeleAction`,
`primeToFiniteAdeleContinuousAction`, its application lemma, and
`primeToFiniteAdeleModule_continuousSMul` give the corresponding constructions
for `PrimeToFiniteAdeles m` acting on `RationalAway A T m`. They use the actual
away residue action and `isOpenEmbedding_away_toRational`. Every natural
modulus is allowed, including zero and one.

The rational vector topology is exactly `rationalTopology A T P`, hence the
final topology of the actual integral Tate limit; the scalar topology is the
existing finite-adele restricted-product topology. All topology and module
instances introduced here are local. No geometric-point, finite-fibre,
finite-etaleness, or order-invertibility assumption is needed for these
continuity results on the previously defined test-point limits. Such
hypotheses remain relevant to their separate geometric finiteness and
compactness assertions. This unit does not construct a restricted product of
local Tate vector spaces, a Weil pairing, or a PEL moduli functor.
