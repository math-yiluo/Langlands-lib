# Equivariant derived sections over varying schemes

This internal construction applies the actual equivariant derived-section
maps of `EtaleDerivedEquivariantMap` to the published
`EquivariantCoefficientDiagram`. It constructs diagrams of group actions in
the bounded-below derived category, with no derived compatibility equation
assumed as input.

Fix a commutative ring `R : Type u`, an indexing category `J : Type v` with
morphism universe `w`, and a scheme diagram `S : J ⥤ Scheme.{u}ᵒᵖ` whose
underlying maps are etale. A group `G : Type t` acts on every vertex through
`ρ i : G →* (Aut (S.obj i).unop)ᵐᵒᵖ`; the input `hρ` states that every scheme
transition is equivariant. Choose the derived localizations of the actual
small-etale module-sheaf categories in a common universe `wS`, independently
of the module localization universe `wT` and the indexing and group universes.

An object `D : EquivariantCoefficientDiagram R S ρ hρ` supplies actual
equivariant coefficient sheaves, equivariant coefficient transition morphisms,
and their sheaf-level identity and composition equations.
`D.derivedSections` has the actual derived-section action of `D.obj i` at
vertex `i`. Its transition along `a : i ⟶ j` is equivariant geometric
derived pullback followed by derived sections of `D.map a`. These transition
maps are equivariant by their construction in the imported map module.
To prove their diagram identity and composition laws, the implementation
forgets the actions and applies the already proved laws of
`D.forget.derivedSections`; equality of action morphisms is detected by their
underlying derived morphisms. No inference from cohomology equality is used.
`derivedSections_map_hom` identifies the underlying transition explicitly.

For a compatible equivariant coefficient morphism `α`, `derivedSectionsMap α`
has at each vertex the derived-section map of `α.app i`, retaining its group
action. Naturality follows from the ordinary derived coefficient-diagram
naturality after forgetting the actions. Pointwise functoriality defines
`derivedSectionsFunctor`.

For `q : ℕ`, `derivedSectionsHomologyIso D q` identifies the action diagram
obtained by applying degree-`q` cohomology with the existing `D.cohomology q`.
Its components are the canonical equivariant derived-to-ordinary comparisons.
Their diagram naturality follows, after forgetting the actions, from the
canonical homology comparison for `D.forget.derivedSections`.
`derivedSectionsHomologyFunctorIso q` makes this comparison natural also
in coefficient diagrams, using the canonical coefficient-natural equivariant
comparison at every vertex. Composing with the published ordinary
degree-zero comparison gives `derivedSectionsZeroIso` and
`derivedSectionsZeroFunctorIso`, recovering the ordinary section diagrams
with their actions in both variables.

This uses ordinary global sections over a fixed scalar ring. Coefficient
transition maps need not be isomorphisms. The group has no topology here.
Compact supports, smoothness, inverse limits, scalar change and the actual
arithmetic Galois and Harris geometric specialization remain separate
construction obligations.
