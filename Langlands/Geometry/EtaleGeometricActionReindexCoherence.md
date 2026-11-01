# Coefficient-natural recovery under geometric action reindexing

This is an internal categorical extension of
`Langlands.Geometry.EtaleGeometricActionReindex`. It constructs the two
coefficient-natural recovery routes for simultaneous level and group reindexing
and proves that they are equal as natural isomorphisms on the entire category
of compatible geometric coefficients. The recovery maps are the canonical maps
already constructed in `EtaleGeometricActionDiagram`.

## Categorical constructions

For categories `J`, `K`, `C`, `B`, a functor `F : K ⥤ J`, monoids `G`, `H`,
a homomorphism `φ : H →* G` and a functor `L : C ⥤ B`,
`actionDiagramMapFunctor J G L` applies `L` to the objects, action morphisms
and equivariant maps of an action-valued diagram. The natural isomorphism
`actionDiagramReindexMapIso` interchanges this operation with level selection
by `F` and action restriction by `φ`. Both orders are definitionally equal;
the comparison is the identity, and `actionDiagramReindexMapIso_app` records
its identity components.

`actionDiagramReindexRecoveryIso` pastes three specified comparisons. Its
inputs are a coefficient functor `r : A ⥤ A'`, diagram-valued functors `E`,
`E'`, `E₀`, a comparison `η` from `r ⋙ E'` to the reindexing of `E`, and a
recovery comparison `χ` from the result of applying `L` to `E` to `E₀`.
The resulting isomorphism first applies `L` to `η`, then the identity
interchange above, then reindexes `χ`. Its component formula removes the
identity interchange and expresses the result as the composite of the two
specified object comparisons. The proof uses extensionality of isomorphisms,
natural transformations and equivariant morphisms, followed by the category
identity law.

The accompanying `naturalIso_ext_app`, whiskering and `mapIso` lemmas expose
these component operations in arbitrary categories. The categorical part uses
arbitrary monoids and independent object and morphism universes for its
categories, as well as independent universes for the two monoids.

## Actual geometric coefficients

Fix a commutative ring `R : Type u`, groups `G`, `H`, and an actual scheme
diagram `S : (J × SingleObj G) ⥤ Schemeᵒᵖ`. A `CoefficientDiagram R S`
contains module sheaves and compatible inverse-image transition morphisms.
The construction uses the existing actual section, derived-section and
ordinary-cohomology functors. Coefficients are reindexed by the product
functor `F.prod (SingleObj.mapHom H G φ)`.

The following names specify both endpoints of the recovery comparisons:

| Functor | Value at a coefficient diagram |
| --- | --- |
| `reindexedDerivedActionHomologyFunctor F φ q` | Reindex the coefficients, take the derived action diagram, then its degree-`q` homology with induced action |
| `restrictedCohomologyActionFunctor F φ q` | Take the original ordinary-cohomology action diagram, then select levels and restrict the group |
| `restrictedSectionsActionFunctor F φ` | Select levels and restrict the original section action diagram |
| `reindexedCohomologyActionFunctor F φ q` | Take ordinary-cohomology actions of the reindexed coefficients |

For homology recovery, `reindexDerivedActionHomologyFirstIso` first compares
the derived action diagrams and then recovers cohomology.
`reindexDerivedActionHomologyRecoveryIso` first recovers cohomology at the
reindexed coefficients and then compares ordinary-cohomology actions.
`reindexDerivedActionFunctorIso_homology` proves equality of these natural
isomorphisms for every nonnegative degree `q`.

The derived degree-zero routes are
`reindexDerivedActionZeroFirstIso` and
`reindexDerivedActionZeroRecoveryIso`; their equality is
`reindexDerivedActionFunctorIso_zero`. These use the specified canonical
comparison from derived degree-zero homology to actual sections.

The ordinary degree-zero routes are
`reindexCohomologyActionZeroFirstIso` and
`reindexCohomologyActionZeroRecoveryIso`; their equality is
`reindexCohomologyActionFunctorIso_zero`. Here the recovery map is precisely
`cohomologyActionZeroFunctorIso`, whose vertex map is the inverse of
`homologyNatIso` followed by `homologyZeroIso`.

Each of the six route constructions has a component formula ending in
`_app`. These recover the corresponding full object-level composites in
`EtaleGeometricActionReindex`. Each equality of coefficient-natural
isomorphisms follows from `naturalIso_ext_app` and the corresponding proved
object-level recovery square. Thus equality includes all compatible
coefficient morphisms, with the original level maps and algebraic actions.
No recovery comparison is added as an assumption.

## Scope and provenance

The geometric part has explicit independent object and morphism universes
for both index categories, independent group universes, a common sheaf
derived-localization universe `wS`, and an independent module
localization universe `wR`. The ring and module carriers are in the scheme
universe `u`. The existing `HasDerivedCategory` instances are required at
each vertex and for `ModuleCat R`. Level maps may be non-etale and
coefficient transition morphisms need not be invertible. No topology on
the groups is used.

This extension derives from the imported actual geometric constructions
and Mathlib's action, functor, whiskering and natural-isomorphism operations.
It is internal coherence infrastructure, not a transcription of a new
literature assertion. Its outputs are algebraic actions on derived module
objects or modules. Realization in a derived representation category,
smoothness, compact supports, tower limits, Galois continuity, arithmetic
coefficients and the Harris specialization remain separate obligations.
