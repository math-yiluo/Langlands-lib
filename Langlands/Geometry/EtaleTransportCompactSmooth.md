# Compact continuous scheme lifts and smooth section sheaves

Author: Worker 13.

This internal scheme construction tests actual transport module sheaves on
genuine compact small-etale schemes equipped with jointly continuous actions
of open subgroups. The topology of every scheme in this construction is its
scheme topology. This is a scheme-side definition, with analytic specialization
and comparison still open.

The inputs are a scheme `Y : Scheme.{u}`, a group `G : Type w` with a topology,
and its opposite-automorphism action `ρ`. Coefficients are in a commutative
ring `R : Type uR`, with module carriers in `Type uM`. All four universes
are independent. No group-smallness or topological-group assumption is
imposed. Smoothness uses open subgroups with the induced topology, without
a topology on the section module.

For `H : OpenSubgroup G`, `compactContinuousProperty ρ H` selects the existing
`LocalAction ρ H` objects whose underlying scheme is compact and for which
`(h,x) ↦ (aut U.action h).hom x` is jointly continuous. `CompactLocalAction`
is the full subcategory with the existing equivariant ordinary etale maps.
Subgroup restriction preserves these conditions by composition with the
continuous subgroup inclusion. A compact base scheme with jointly continuous
operators gives the constructed whole-scheme test for every open subgroup.

`CompactSmooth.IsSmoothSheaf` requires that the actual section representation
on every such test be smooth, using the open-subgroup fixed-vector definition
already in the Library. Its full subcategory keeps actual transport sheaves
and all sheaf natural transformations. It is closed under subobjects:
evaluation representations preserve finite limits, so a sheaf monomorphism
induces an injective intertwiner on every test, and smoothness descends along
that injective intertwiner. Consequently the property is invariant under
isomorphisms. If `G` is discrete, the trivial subgroup fixes every vector
and is open in each test subgroup, so every transport module sheaf satisfies
the condition.

The property is also closed under finite limits. For a finite diagram of
qualifying sheaves and a fixed test, the existing local evaluation
representation preserves the sheaf limit. Lift the evaluated diagram to
the smooth representation category. That category has finite limits, and
its exact inclusion into algebraic representations preserves them.
Uniqueness of limits identifies the evaluated sheaf limit with the
forgotten smooth representation limit, so smoothness transfers along this
isomorphism. This supplies finite limits in the full sheaf subcategory
and finite-limit preservation by `inclusion`, without any sheafification
or smallness hypothesis.

For every test, `sections` retains the complete original section
representation and its proved smoothness. `sectionsForgetIso` recovers exactly
the original evaluation representation after forgetting smoothness. It does
not replace that section module by its smooth submodule. Equivariant etale
maps give the actual restriction intertwiners; these form the contravariant
`sectionDiagram`. The section functors are additive and preserve finite
limits. The latter follows by composing with the fully faithful,
limit-reflecting inclusion into algebraic representations.

Assume that `Y` is compact and the original `G`-action on its scheme
topology is jointly continuous. `wholeSectionsForgetIso` identifies the
forgotten sections on the whole-scheme test for `H` with the existing
global section representation restricted along `H.subtype`. The whole
test at the full open subgroup proves smoothness of all global sections:
pull its smooth representation back along the continuous homomorphism
`G → ⊤` that sends `g` to `⟨g, trivial⟩`. This composite is the original
global section action. `globalSections` therefore keeps the full global
section representation with this proved smoothness.
`globalSectionsForgetIso` recovers the original global representation.
This functor is also additive and preserves finite limits.

The provenance is internal assembly of actual scheme transport actions,
compactness and joint continuity, the existing open-stabilizer predicate,
the existing actual sheaf evaluation representations, and finite limits
and exact forgetting in the smooth representation category. No
external-source definition or theorem is claimed verbatim.

The tests use the scheme topology. Analytic sites, analytic local-lift
existence and comparison with a smooth analytic sheaf category remain
separate obligations. The scheme category is not asserted to provide that
specialization.
It makes no abelianity, quotient closure, enough-injectives, Godement,
compact-support cohomology or Harris comparison claim for this subcategory.
