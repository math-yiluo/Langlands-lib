# Continuous transport on actual rational Tate modules

This internal construction equips the existing rational base-change, geometric
path, and invertible rational-homomorphism comparisons with continuity. Its
provenance is the published integral comparisons, the final-topology universal
property in `Langlands.Topology.Rationalization.Basic`, and the actual
`RationalTopology` specialization. It is not a transcription of a separate
literature theorem.

All topologies in this file are the named `rationalTopology`, installed locally:
the final topology of the charts from the actual integral inverse limit into its
rationalization. No global topology instance on tensor products is registered.

## Base change and paths

For every morphism of base schemes, abelian scheme on the target base, test
scheme over the source base, and predicate selecting positive torsion orders,
`rationalBaseChangeContinuousLinearEquiv` bundles the existing
`rationalBaseChange` as a continuous rational-linear equivalence. Both directions
are the rational scalar extensions of the published continuous integral
comparisons. The generic `continuous_baseChange` theorem proves continuity.
This requires no finite-fibre or retained-order invertibility hypothesis.

`rationalTransportContinuousLinearEquiv` bundles the existing transport along a
supplied natural isomorphism between the actual finite-étale fibre functors.
The two field-valued points may have different fields. Finite-fibre witnesses,
the explicit `TorsionFiniteEtaleStatement` proposition, and invertibility of
every retained positive order are the same inputs as in `rationalTransport`.
The forward continuity proof extends the continuous integral path map; the
inverse uses the reverse path. No existence of a path is asserted here.

The projection lemmas state that forgetting continuity gives exactly the
existing rational linear equivalences. Thus the previously proved algebraic
coherence, scalar compatibility, and naturality refer to these same functions.

## Rational homomorphisms

`continuous_rationalHomMap` proves continuity of the map associated to an
element of the actual rationalized homomorphism group, provided the target
selected rational Tate group has continuous addition. The implemented proof
uses tensor-product induction on the homomorphism: a pure tensor is a fixed
rational multiple of a continuous homomorphism-induced Tate map, and addition
uses continuous addition in the target.

The full and away specializations discharge this topological-group premise
using `rationalFull_topologicalAddGroup` and
`rationalAway_topologicalAddGroup`. They work at every test scheme and for
every natural away modulus, including zero and one.

`rationalIsoContinuousLinearEquiv` bundles the existing `rationalIso`, with the
same topological-group premise at both endpoints. The maps come from the
isomorphism and its inverse in the rationalized category. The full and away
versions discharge both premises and give continuous rational-linear
equivalences without extra geometric hypotheses. Their projection lemmas
identify the underlying equivalences with the previously defined `rationalIso`.

This unit makes no assertion of joint continuity for finite-adelic scalars,
continuity of the homomorphism parameter, a topological restricted-product
identification, pairing compatibility, or canonical independence of a chosen
path.
