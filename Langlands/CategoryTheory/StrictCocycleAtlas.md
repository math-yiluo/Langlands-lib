# Strict partial cocycle atlases

This is an internal construction for gluing arguments in which transitions must
be preserved exactly when more charts are added. Its provenance is the elementary
finite-character argument for unions of chains, followed by Mathlib's Zorn
lemma. It introduces no geometric premise or literature-dependent definition.

Fix a type `I` of charts, a type `T i j` of possible transitions for each ordered
pair, a predicate `C i j k eij ejk eik` expressing triple compatibility, and a
distinguished chart `i₀`. A label is either a vertex or an actual transition with
its endpoints. `Good C i₀ S` says that a set of labels contains the distinguished
vertex, every transition's endpoints, exactly one transition for every ordered
pair of present vertices, and the compatibility predicate for every ordered
triple of present edges. Repeated indices are included.

The domain of an atlas is the set of its vertices. `transition` selects its
unique transition for each ordered pair, and `transition_cocycle` verifies the
given compatibility predicate for those selected transitions. The order is
ordinary inclusion of label sets. Thus the lemma `transition_preserved` gives
equality of the old and new transitions, not merely an isomorphism between
different choices of transitions.

For a nonempty chain of good label sets, `good_sUnion` proves that their union is
good. Each condition involves at most three labels. Directedness of a chain puts
all those labels in one member, where the required condition holds. For the
existence of a transition, the two vertex labels are first put in one member,
and that member supplies the edge. Zorn's lemma then yields
`exists_maximal_extension`; `maximalExtension` chooses such an extension of the
given atlas.

The definition `graph` encodes a domain and an explicit transition family as
labels. A family satisfying the compatibility predicate has a good graph, and
`graph_transition` recovers a good atlas from its domain and selected
transitions. The lemma `subset_graph` verifies strict extension by an explicit
larger family whose transitions agree with the old ones.
Consequently, `maximal_domain` says that a coherent strict extension of a
maximal atlas cannot introduce a new chart.

Chart and transition types may live in independent universes. This construction
does not supply initial geometric cocycles, new charts, local extensions, or
the claim that a maximal geometric atlas covers its target.
