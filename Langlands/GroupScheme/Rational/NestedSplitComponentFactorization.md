# Split-component factors through an intermediate group

Worker 17. This internal construction starts with a compatible root presentation
of a fine ambient parabolic and its original Levi `M`, a closed intermediate
group `L` containing that Levi, and a central map from a commutative group scheme
`A` to `L`. The defining cocharacter supplied by the presentation lies in `M`.
Centrality in `L` puts the map into its ambient centralizer, which is exactly the
fine Levi image on every test scheme. The represented-subgroup factor constructs
`intermediateCentralFactor`; cancellation of the closed intermediate inclusion
proves its composite is the original map. Its centrality is reflected by the
fine Levi inclusion.

If `A` is split, maximality of the specified fine Levi split component `B`
factors this lifted central map through `B`. The construction
`intermediateSplitComponentFactor : A ⟶ B` chooses this actual scheme map, and
`intermediateSplitComponentFactor_comp` proves its compatibility with the
original inclusion into `L`.

The field universe and characteristic are arbitrary. A compatible fine ambient
presentation is an explicit input. No presentation of a parabolic of `L`,
dynamic structure statement, or root-cone comparison is inferred. These are
derived facts about published group-scheme constructions, intended for central
restriction of exponents in Renard VII.2.3; they do not prove temperedness or
square-integrability.
