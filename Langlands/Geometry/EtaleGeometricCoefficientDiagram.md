# Compatible coefficients over arbitrary scheme diagrams

This internal construction assembles the actual geometric inverse-image
coefficient maps into diagrams of bounded-below derived sections, ordinary
cohomology and global sections. The schemes and their morphisms are arbitrary.
The coefficient inputs are genuine sheaves and sheaf morphisms with their
identity and composition laws. All cohomological maps and their functoriality
are constructed and proved.

The main namespace is `Langlands.Geometry.EtaleGeometricDiagram`. Let
`J : Type v` have a category structure with morphisms in universe `w`, let
`S : J ⥤ Scheme.{u}ᵒᵖ`, and let `R : Type u` be a commutative ring. Write
`Xᵢ = (S.obj i).unop`. An arrow `a : i ⟶ j` induces a scheme morphism
`fₐ = (S.map a).unop : Xⱼ ⟶ Xᵢ`. There is no étaleness hypothesis.
`ModuleSheaf Xᵢ R` is the existing category of module sheaves on the actual
small étale site; the underlying coefficient modules have universe `u`.
There are no field, finiteness, Noetherian or local-constancy assumptions.

## Geometric coefficient data

`diagramInverseImage R S a` is the actual geometric inverse-image functor
`fₐ⁻¹`, constructed in `EtaleInverseImage`. The identity comparison
`diagramInverseImageId` first transports the equality `S.map_id`, then uses
`inverseImageId`. The composition comparison `diagramInverseImageComp`
has direction

```text
fₐ⁻¹ ⋙ fᵦ⁻¹ ≅ f₍ₐ≫ᵦ₎⁻¹.
```

It combines `inverseImageComp` with the inverse of the equality transport
coming from `S.map_comp`. The functor's identity and composition equalities
are therefore retained in the coefficient types, rather than silently
treated as definitional equalities.

`CoefficientDiagram R S` consists of a sheaf `D.obj i` on each `Xᵢ` and a
morphism

```text
D.map a : fₐ⁻¹(D.obj i) → D.obj j
```

for every arrow, subject to the actual sheaf-level identity law and

```text
diagramInverseImageComp.hom ≫ D.map (a ≫ b)
  = fᵦ⁻¹.map (D.map a) ≫ D.map b.
```

The transition maps need not be isomorphisms. A morphism `α : D ⟶ E` is a
family of sheaf morphisms `α.app i` satisfying

```text
D.map a ≫ α.app j = fₐ⁻¹.map (α.app i) ≫ E.map a.
```

`Hom.id` and `Hom.comp` are pointwise identity and composition; their
commutativity conditions follow from functoriality. The category laws are
proved pointwise. `CoefficientDiagram.evaluation i` returns the actual
sheaf and sheaf morphism at a vertex. These coefficient constructions
require no derived-category localization.

The auxiliary theorem `EtaleInverseImage.inverseImageCongr_refl` proves
that the previously constructed geometric equality comparison for `rfl`
is the identity isomorphism. Its proof applies the injective adjunction-mate
correspondence, identifies the conjugate with geometric direct-image
transport, and checks that reflexive pullback transport is the identity
using the two projections of the actual fiber product. Applying the
coefficient presheaf to that identity finishes the proof.

## Derived sections

For the remaining constructions assume
`HasDerivedCategory.{wS} (ModuleSheaf Xᵢ R)` for every vertex and
`HasDerivedCategory.{wR} (ModuleCat.{u} R)`. The sheaf-localization universe
`wS` is common to the vertices; the module-localization universe `wR` is
independent of it and of `u`, `v`, and `w`.

`sheafDerivedPullback_congr` proves that changing a scheme morphism by an
equality changes its derived geometric pullback by exactly
`inverseImageCongr`. The proof reduces the equality to reflexivity and
uses the preceding theorem. `diagramDerivedPullback_id` and
`diagramDerivedPullback_comp` then combine this equality transport with
the existing geometric identity and composition laws.

`D.derivedSections : J ⥤ DerivedCategory.Plus (ModuleCat R)` has object
`RΓ(Xᵢ,D.obj i)`, with the sheaf embedded in degree zero. Its arrow map is
the existing geometric coefficient pullback

```text
RΓ(Xᵢ,D.obj i) → RΓ(Xⱼ,fₐ⁻¹(D.obj i)) → RΓ(Xⱼ,D.obj j).
```

The identity proof uses `D.map_id` and `diagramDerivedPullback_id`. The
composition proof uses `D.map_comp`, the geometric composition equation
and naturality of derived pullback at `D.map a`.
`derivedSectionsMap α` applies actual derived sections to each `α.app i`;
its naturality uses `α.comm` and the geometric pullback naturality square.
`derivedSectionsFunctor` packages these maps as a functor in compatible
coefficients, with identity and composition proved pointwise.

## Ordinary cohomology and sections

For every `q : ℕ`, `D.cohomology q` has the actual ordinary right-derived
cohomology module `Hᵠ(Xᵢ,D.obj i)` at each vertex. Its arrow map is defined
by transporting degree-`q` homology of `D.derivedSections.map a` through
the canonical source and target `homologyNatIso` isomorphisms.
Functoriality follows by cancellation of these isomorphisms and
functoriality of homology.

`cohomology_map` proves that this transported map equals the constructed
`cohomologyPullbackWithCoefficients fₐ R q (D.map a)`. Its proof uses the
existing coefficient-pullback homology square and cancels the source
identification. Thus the arrow map is identified with the actual geometric
ordinary-cohomology map, with the given target coefficient morphism.
`derivedSectionsHomologyIso D q` is the resulting natural isomorphism
between degree-`q` homology of the derived diagram and `D.cohomology q`.

`cohomologyFunctor q` acts on a coefficient morphism by
`cohomology Xᵢ R q` applied to `α.app i`. Its naturality is proved using
`cohomology_map`, `α.comm` and geometric cohomology naturality.
`cohomologyFunctor_map_app` records the component formula.
`derivedSectionsHomologyFunctorIso q` proves that the preceding homology
recovery is natural also in the coefficient diagram.

`D.sections` similarly has actual global sections at each vertex, with
arrows transported from degree-zero derived homology through
`homologyZeroIso`. `sections_map` proves equality with
`sectionsPullbackWithCoefficients fₐ R (D.map a)`, using the already
proved geometric degree-zero recovery square.
`derivedSectionsZeroIso` is natural in the diagram arrows.
`sectionsFunctor` applies actual global sections to coefficient morphisms,
as recorded in `sectionsFunctor_map_app`; its naturality uses
`sections_map` and the geometric section-pullback square.
`derivedSectionsZeroFunctorIso` proves recovery natural in coefficients.
Finally, `cohomologyZeroFunctorIso` identifies degree-zero ordinary
cohomology with actual sections naturally in both variables, by composing
the two derived-homology comparisons.

In this module the section diagrams and their functor use the stated
localization instances because they are defined by derived-homology
transport. Their underlying vertex objects and the identified geometric
section maps are the existing global-section constructions.

## Provenance and remaining specialization

The provenance is internal: this is categorical assembly of the existing
geometric inverse image, its equality and composition comparisons, derived
geometric pullback, ordinary cohomology and degree-zero normalization. The
coefficient category generalizes the existing restriction-based diagram
construction to arbitrary scheme morphisms. No new external literature
assertion is made.

The construction requires an actual compatible sheaf diagram as input; it
does not construct a coefficient sheaf from arithmetic data. Comparison
with the previous restriction-based diagrams for étale scheme maps,
scalar-change coherence, tower limits, compact support, smooth group and
Galois actions, and the Shimura and analytic specialization required by
Harris remain separate constructions.
