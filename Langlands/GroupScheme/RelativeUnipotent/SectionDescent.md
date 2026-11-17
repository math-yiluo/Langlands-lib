# Descent for the canonical relative-section pullback

This internal supporting construction concerns a module sheaf `M` on an arbitrary
scheme `S`, all in universe `u`. For a test `T` over `S`, the section object is
`GlobalSections ((Scheme.Modules.pullback T.hom).obj M)`. Every section map is
exactly `RelativeUnipotent.sectionPullback M`, with the canonical composition
and equality comparisons prescribed in the target definitions.

For an arrow `b : U ⟶ T` over `S`, `SectionCompatible M b s` asserts the matching
equation on every test `W` over `S`: whenever `a c : W ⟶ U` satisfy
`a ≫ b = c ≫ b`, the relative pullbacks of `s` along `a` and `c` agree.
`existsUnique_section_of_compatible` proves that such a section descends uniquely
if the underlying map of `b` is affine, flat and surjective and `M` is
quasi-coherent. `sectionOfCompatible` chooses that unique section, and
`sectionPullback_sectionOfCompatible` identifies its pullback with the input.
There is no affine-base, noetherian, finite-presentation, constant-rank or
nonempty-base assumption.

The proof first establishes composition of the prescribed relative pullback by
naturality of actual section pullback and associativity of the canonical module
comparisons. A flat surjective test map detects equality of relative sections:
raw pullback is injective and the final comparison is an isomorphism. Neither
this injectivity result nor the composition result requires quasi-coherence.

The cover section is then normalized by the inverse comparison to a section of
the iterated ordinary pullback sheaf. `iteratedSection_pullback` transports any
further raw pullback to a common composite and identifies the result with the
original relative section pullback. The actual equal-composite comparison is
the first composition comparison followed by the inverse of the second.
Consequently the relative matching equation implies the genuine raw-module
overlap equation. Every raw scheme test obtains a structure map to `S` from its
map to `U`, so restricting this argument to tests over `S` loses no overlap
equations. The ordinary section-descent theorem in `FlatSectionDescent` descends
the normalized section. The comparison then gives the claimed relative
pullback equation, and injectivity proves uniqueness.

This is derived content from the actual section, pullback-comparison and
faithfully flat section-descent interfaces. It introduces no external structural
claim or effectivity assumption. Constructing compatible group-point/section
equivalences and proving the parent relative radical-filtration statement remain
further obligations.
