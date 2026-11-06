# Exact qualitative reduction for dynamic-parabolic compression

Worker 1751. This internal reduction compares the existing Library proposition
`UniformCompressionStabilizationStatement.{u,v}` with the new qualitative
`PointwiseCompressionStabilizationStatement.{u,v}`. It proves their equivalence
and establishes neither proposition unconditionally.

The new statement repeats exactly the original geometric context: a connected
reductive group scheme over a nonarchimedean local field, actual rational-point
topology, local compactness and the nonarchimedean group condition, the dynamic
parabolic of a cocharacter, a compact open subgroup, and a group element central
in the dynamic Levi and satisfying the actual Iwahori contraction conditions
for the positive and negative dynamic radicals. Its conclusion asks for eventual
stability of the compressed action on every smooth representation in the fixed
carrier universe. The field and carrier universes remain independent. No
admissibility, finite generation or dimension premise is added.

In the forward implication the proof applies the supplied uniform statement to
the underlying carrier and representation of each bundled smooth object. Its
stationary-chain and complementarity conclusion gives eventual stability by the
fixed-exponent interface. In the reverse implication, the qualitative hypothesis
feeds the actual countable-direct-sum diagonal reduction, producing one threshold
before all bundled smooth objects. Bundling an arbitrary smooth representation
as `SmoothRep.of` then yields the exact original conclusion with that same
threshold, both stationary power-chain equalities, and complementarity.

The dynamic-parabolic, centrality and contraction premises are passed unchanged
through this equivalence. The representation-theoretic proof that they imply
qualitative eventual stability remains an obligation. The diagonal argument
itself uses only smooth sums and compression naturality.

The source context is Renard 2026, VI.9.1 Proposition, printed p.197 / PDF p.203,
and Appendix C.II, Definition and Lemma (iv), printed pp.276–278 /
PDF pp.282–284. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
This equivalence is an internal alternative route to the uniformity step and is
not attributed to Renard's quantitative proof.
