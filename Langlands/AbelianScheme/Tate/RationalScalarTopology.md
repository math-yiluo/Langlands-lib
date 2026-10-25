# Topology of the normalized Tate scalar comparisons

This internal construction upgrades the existing normalized scalar witnesses
from `RationalScalars` and `AwayRationalScalars` to homeomorphisms. The proof
combines their stated integral continuity with openness of the actual integral
finite-adele subrings and the generic construction in
`Langlands.Topology.Rationalization.Comparison`. It adds no new comparison
existence hypothesis and makes no new claim from external literature.

In `Langlands.Global.RationalProfiniteIntegerAdeleComparison`, fix the explicit
comparison proposition `h`. The definition `integralHomeomorph h` has underlying
ring equivalence `integralEquiv h`, chosen from that same `h`. Its continuity
and inverse continuity are the corresponding conjuncts of `h`.
`isOpenEmbedding_integralEquiv` composes this homeomorphism with the inclusion
of `integralFiniteAdeles ℚ` into `FiniteAdeles ℚ`. That inclusion is an open
embedding for the existing restricted-product topology.

The definition `rationalHomeomorph h` is

\[
\mathbb Q\otimes_{\mathbb Z}\mathrm{ProfiniteIntegerRing}
  \simeq_{\mathrm{top}} \mathrm{FiniteAdeles}(\mathbb Q).
\]

Its source carries `Langlands.Topology.Rationalization.finalTopology`; its
target carries the existing finite-adele topology. Its underlying map is
exactly `rationalEquiv h`, with the same inverse. The normalization on pure
tensors required by the generic comparison is `rationalEquiv_tmul h`:

\[
q\otimes a \longmapsto
\operatorname{algebraMap}(q)\,\mathrm{integralEquiv}(h)(a).
\]

The application lemmas record the equality of underlying maps in both
directions. `continuous_rationalEquiv` and `continuous_rationalEquiv_symm`
expose the two continuity conclusions without requiring clients to use the
homeomorphism bundle.

In `Langlands.Global.PrimeToRationalProfiniteIntegerAdeleComparison`, the
definitions and continuity lemmas have the same names. They take
`hAway : PrimeToRationalProfiniteIntegerAdeleComparison h m`, retaining its
coupling to the full witness `h`. The resulting comparison is

\[
\mathbb Q\otimes_{\mathbb Z}\mathrm{PrimeToProfiniteIntegerRing}(m)
  \simeq_{\mathrm{top}} \mathrm{PrimeToFiniteAdeles}(m).
\]

Here the integral inclusion is open by `isOpen_primeToIntegralFiniteAdeles m`.
The source again has the final rationalization topology and the target has
the existing restricted-product topology. The modulus is any natural number,
including zero and one; no primality hypothesis or nontriviality of the
target is introduced.

`rationalHomeomorph_restrict` and `rationalHomeomorph_symm_restrict` state the
full-to-away commuting squares for these exact maps. They reuse the existing
algebraic restriction equations, since the new homeomorphisms retain the
same underlying equivalences. In particular, the forward square compares
rationalization of residue restriction with `primeToFiniteRestriction m`.

All comparison propositions remain explicit parameters. This file proves
topological properties of the scalar comparisons; it does not construct the
comparison between rational Tate vectors and a restricted product of local
Tate modules, establish joint continuity of their scalar action, or discharge
the geometric or Weil-pairing obligations of the surrounding PEL construction.
