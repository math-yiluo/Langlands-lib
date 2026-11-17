# Descent of actual sections along affine flat surjections

This internal supporting construction descends a global section of the actual
pullback of a quasi-coherent module sheaf along an affine, flat, surjective
scheme morphism. Compatibility means equality after the actual canonical
equal-composite pullback comparisons on every scheme test. No local finite
presentation, noetherian, affine-base or constant-rank hypothesis is imposed.

The proof converts the cover section into a morphism from the pullback of the
unit sheaf. The canonical overlap comparison respects the actual unit
trivializations. Thus the section compatibility equations give exactly the
ordinary-module morphism compatibility equations. The published faithful flat
morphism descent theorem produces a morphism from the unit downstairs.
The section/unit-morphism equivalence produces the descended section.

Faithfulness of pullback along a flat surjection proves uniqueness, and also
gives `pullbackSection_injective` for an arbitrary module sheaf without
quasi-coherence. `sectionOfCompatible` chooses the unique descended section;
its pullback lemma identifies its actual pullback with the input section.
`pullbackSectionAddHom` records additivity of the same actual section map.

The provenance is internal and derived from the published ordinary-module
morphism descent theorem, the equal-composite unit comparison, and the actual
section/unit-morphism equivalence. No external structural result or assumed
effectivity premise is introduced. This is a section-descent ingredient for
linear-chart descent; it does not itself construct group-point equivalences,
a relative unipotent radical filtration or its successive quotients.
