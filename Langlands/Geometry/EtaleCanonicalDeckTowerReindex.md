# Reindexing canonical cohomological consumers of over-base deck towers

This module specializes the existing coefficient-natural reindexing comparisons
to the actual geometric input of `EtaleCanonicalDeckTower`. It constructs
comparisons for derived global sections, ordinary cohomology in every natural
degree, and global sections, naturally in every original base sheaf and its
morphisms. It also proves compatibility with the three specified homology and
degree-zero recovery comparisons.

## Inputs and conventions

Let `X : Scheme.{u}`, let `R : Type u` be any commutative ring, and let
`A : J ⥤ Action ((Over X)ᵒᵖ) G` be an actual functor. Thus the input includes the
original schemes over `X`, their algebraic `G`-actions, the contravariant level
maps, equivariance, functor laws, and over-base triangles. The module uses the
canonical inverse-image coefficients already constructed from these data. It
does not ask for coefficient cocycles, cohomology objects or cohomological
compatibility witnesses.

For an arbitrary functor `F : K ⥤ J` and group homomorphism `φ : H →* G`,
`reindex A F φ` selects the original level `F.obj i` and restricts its action
along `φ`. Neither `F` nor `φ` has to be injective, surjective, finite or an
equivalence. The level categories have independent object and morphism universes,
and the two groups have independent universes. Schemes, the coefficient ring,
and coefficient modules use `u`; the two derived-category universes are
independent.

All three current consumers and their comparisons, including global sections,
use the existing `HasDerivedCategory` instances for the small-etale module-sheaf
categories at all original product vertices and for `ModuleCat.{u} R`. The
selected instances are obtained by evaluation at the original vertices; no
independent existence premise is added for the reindexed geometry. The section
action and level maps inherit these assumptions because the published
coefficient-diagram construction obtains them through derived homology.

The groups are abstract algebraic groups. The module imposes no etaleness,
finiteness, properness, freeness, transitivity or covering hypothesis on the
geometry. The word “deck” retains the parent module's meaning of an over-base
automorphism, with no torsor assertion. No topology, continuity or smoothness of
the resulting group actions is asserted.

## Canonical coefficient equality and the three comparisons

Write `C_A` for `coefficientFunctor R A`, `Q` for coefficient-diagram reindexing
along `F.prod (SingleObj.mapHom H G φ)`, and `T_D` for
`actionDiagramReindexFunctor F φ D`. The equation
`coefficientFunctor_reindex_eq` identifies `C_(reindex A F φ)` with `C_A ⋙ Q`.
It follows definitionally from retaining the same original inverse images and
all their transition and coefficient maps.

For each consumer the module names both endpoint functors:

| Consumer | Reindexed original geometry | Selected levels and restricted action |
| --- | --- | --- |
| Derived sections | `reindexedDerivedFunctor` | `restrictedDerivedFunctor` |
| Ordinary cohomology | `reindexedCohomologyFunctor q` | `restrictedCohomologyFunctor q` |
| Global sections | `reindexedSectionsFunctor` | `restrictedSectionsFunctor` |

The reindexed endpoint is the corresponding parent-module consumer of
`reindex A F φ`. The restricted endpoint is the parent-module consumer of `A`
followed by `T_D`. These names retain the actual functors, including every
original base-sheaf morphism; they introduce no extra input.

The natural isomorphisms
`reindexDerivedFunctorIso`, `reindexCohomologyFunctorIso q` and
`reindexSectionsFunctorIso` identify the two endpoints. Their construction
has three parts. First, map the existing canonical coefficient reindexing
isomorphism through the relevant coefficient-diagram consumer and insert the
explicit functor associator; these are the three `*SourceIso` definitions.
Next, left-whisker the existing generic coefficient-natural reindexing
isomorphism by `C_A`; these are the three `generic*ReindexIso` definitions.
Finally, use the inverse associator to reach the named restricted endpoint.
Consequently each comparison is natural in every morphism of original base
sheaves, natural along every selected level arrow, and `H`-equivariant.

## Original-object components

For a base sheaf `M` and `i : K`, put `Y = (A.obj (F.obj i)).V.unop.left` and
`p = (A.obj (F.obj i)).V.unop.hom : Y ⟶ X`. The three
`reindex*FunctorIso_hom_app_app_hom` lemmas prove that the underlying forward
component is the identity on, respectively:

- `EtaleDerivedSectionsPlus.derivedSections Y R` applied to `p`-inverse-image of
  `M`;
- `EtaleDerivedSections.cohomology Y R q` applied to that same sheaf;
- `EtaleDerivedSections.sections Y R` applied to that same sheaf.

These are identities on the actual original-scheme objects. The isomorphisms
still identify the full action diagrams, whose actions and level maps come from
the parent module's original geometric pullbacks.

The implemented component proofs first project the mapped coefficient
comparison. The existing consumer Hom formula and identity coefficient
components reduce it to the functor identity law. The generic comparison
component is obtained by projecting the existing functor-isomorphism component
formula and applying its object-level identity lemma. Composition with the
associator identity components proves the stated final formulas.

## Recovery coherence

The three coherence lemmas are equalities of natural isomorphisms of
`K`-indexed `H`-action diagrams, evaluated at each arbitrary base sheaf `M`:

- `reindexDerivedFunctorIso_homology q M` equates the route “reindex derived
  sections, then apply the original homology recovery at selected levels” with
  “apply homology recovery on the reindexed geometry, then reindex ordinary
  cohomology.”
- `reindexDerivedFunctorIso_zero M` gives the corresponding square for the
  parent's canonical derived degree-zero comparison with global sections.
- `reindexCohomologyFunctorIso_zero M` gives the square for the parent's
  canonical ordinary degree-zero comparison with global sections.

Thus these squares preserve the specified comparisons, including the ordinary
degree-zero map given by the inverse homology comparison followed by the
canonical section comparison. They do not choose replacement isomorphisms.
All constituent comparisons are natural in base coefficients. The displayed
equalities themselves are stated after evaluation at `M`.

The proofs use extensionality of isomorphisms, natural transformations and action
morphisms. At an original level they substitute the proved identity components,
expose the parent's original-scheme recovery formulas, and apply the functor
identity and categorical identity laws.

## Provenance and remaining scope

This is an internal categorical specialization, with no new claim attributed to
an external source. It imports `EtaleCanonicalDeckTower` and reuses its actual
geometry, canonical inverse-image coefficients, and cohomological consumers.
Its generic comparison input is the existing construction in
`EtaleGeometricActionReindex`; its coefficient comparison comes from
`EtaleCanonicalCoefficientDiagram`. The explicit associators are Mathlib's
functor associators. The source comparison is constructed from coefficient
maps, rather than supplied as a desired cohomological compatibility.

This completes the specialized consumer reindexing obligation retained by
`EtaleCanonicalDeckTower`. It does not construct a new Shimura or arithmetic
tower, identify Hecke or Galois actions, supply an analytic-etale realization,
or prove a compact-support, trace or Harris comparison theorem. Those
specializations and the remaining host-task constructions are still required.
