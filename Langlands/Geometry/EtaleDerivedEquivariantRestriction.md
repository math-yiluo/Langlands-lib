# Group restriction of actual derived equivariant diagrams

This internal construction combines the actual varying-scheme derived action
diagrams of `EtaleDerivedEquivariantDiagram`, the coefficient restriction
functor of `EtaleEquivariantCoefficientRestriction`, and the derived
single-scheme restriction comparisons of `EtaleDerivedActionRestriction`.
It proves the induced diagram comparisons from those constructions.

Let `S : J ⥤ Scheme.{u}ᵒᵖ` be a diagram whose underlying scheme maps are
etale, and let `R : Type u` be a commutative ring. At each vertex, an
abstract group `G` acts by `ρ i`, compatibly with the scheme arrows as
specified by `hρ`. A compatible equivariant coefficient diagram `D` has
actual small-etale module sheaves and equivariant coefficient transitions.
The transitions may be noninvertible. For a group homomorphism
`φ : H →* G`, restriction retains the underlying sheaves and transitions.
The two group universes and both index-category universes are independent.
The vertex sheaf categories use one common derived-localization universe,
independently of the derived-localization universe for modules.

`restrictGroupDerivedSectionsIso` identifies derived sections of the
restricted coefficients with the original derived action diagram followed
by `Action.res` along `φ`. Its components are the constructed
`restrictionDerivedSectionsFunctorIso` components. Their underlying
derived maps are identities, as recorded by
`restrictGroupDerivedSectionsIso_hom_app_hom`. Naturality along geometric
arrows follows because restriction retains the full ordinary coefficient
diagram, hence the underlying derived transitions agree.
`restrictGroupDerivedSectionsFunctorIso` promotes this to a natural
isomorphism in compatible coefficient diagrams, using the single-scheme
comparison's coefficient naturality at each vertex.

For each `q : ℕ`, `restrictGroup_derivedHomology` proves that this comparison
commutes with canonical recovery of the ordinary cohomology action diagram
and its published group-restriction comparison.
`restrictGroup_derivedZero` gives the analogous equation for ordinary
sections. Both are equations of natural transformations of diagrams,
proved by their single-scheme equations at every vertex. These arguments
do not infer equality of derived maps from equality of their cohomology.

The construction uses ordinary global sections of coefficient sheaves
placed in degree zero, with a fixed scalar ring and abstract groups.
It constructs no compact supports, traces, smoothness, continuity,
scalar change, inverse limits, or arithmetic/Harris specialization.
