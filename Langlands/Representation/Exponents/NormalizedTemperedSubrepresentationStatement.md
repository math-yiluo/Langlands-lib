# Subrepresentation closure of normalized-exponent temperedness

This derived supporting statement isolates the subrepresentation step used in
Renard, *Représentations des groupes réductifs p-adiques*, version of 9 July
2026, VII.2.6, Theorem, printed page 231 / PDF page 237. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

`NormalizedTemperedSubrepresentationStatement` says that if a smooth
representation embeds by an injective intertwiner into a representation
satisfying the published `IsNormalizedExponentTempered` predicate, then it also
satisfies that predicate. No irreducibility is assumed.

The statement quantifies over the same arbitrary local-field universe and an
independent carrier universe as the VII.2.6 targets. It retains the canonical
topology on rational points, local compactness and the nonarchimedean-group
instance. The temperedness predicate includes admissibility and compatible-root
presentation coverage for every actual rational parabolic, rational Levi and
split component. No extra presentation-existence, compact-exhaustion,
Jacquet-admissibility or quotient-compactness premise is added.

This is an internal interface for a step of the source argument, rather than a
separate numbered source assertion. The source uses exactness of Jacquet functors
to pass temperedness to a subrepresentation. A proof can identify each matching
geometric radical with a dynamic unipotent subgroup using the presentations
already supplied by target temperedness, apply published compact containment and
normalized Jacquet injectivity, and transport generalized weights. This module
states the interface; it does not prove it or any of the three VII.2.6 targets.
