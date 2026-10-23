# Fixed-scheme specialization of compatible coefficient diagrams

This module connects the varying-scheme construction in
`EtaleCohomologyDiagramFunctor` to the existing fixed-scheme functor
`EtaleDerivedSections.diagramFunctor`. An ordinary diagram of actual
module sheaves on one scheme determines compatible coefficients on the
constant scheme diagram. The resulting cohomology agrees with the
existing construction naturally in every coefficient diagram and every
cohomological degree.

Fix `X : Scheme.{u}`, a commutative ring `R : Type u`, and
`J : Type v` with morphisms in universe `w`. Coefficient sheaves are
`EtaleDerivedSections.ModuleSheaf X R`, the actual small-étale sheaves
valued in `ModuleCat.{u} R`. The declarations are in
`Langlands.Geometry.EtalePullback`; the coefficient constructions and
comparisons are in its `CoefficientDiagram` namespace.

## The constant scheme and restriction coherence

`fixedSchemeDiagram X J : J ⥤ Scheme.{u}ᵒᵖ` is the constant functor
with value `op X`. Every arrow maps to the identity scheme morphism,
so all its arrows have the required étaleness instances without an
additional geometric hypothesis.

Restriction along `𝟙 X` is identified with the identity on sheaves
by `EtalePullback.restrictionId`. It is not replaced by a definitionally
strict identity. Write `T` for this restriction functor and `u : T ≅ 𝟭 _`
for the identification. `fixedSchemeDiagram_restrictionId` identifies
the imported `diagramRestrictionId` with `u`.

For arrows `a : i ⟶ j` and `b : j ⟶ k`, let `c` be the imported
`diagramRestrictionComp` for the constant scheme diagram.
`fixedSchemeDiagram_restrictionComp` proves the coherence identity

```text
c.hom.app F ≫ u.hom.app F = T.map (u.hom.app F) ≫ u.hom.app F.
```

The proof identifies the first factors as actual sheaf maps, using
extensionality on the underlying presheaf natural transformation. At
each étale object the maps are definitionally identical. Thus this
coherence is established by the constructed restriction identifications;
it is not assumed as extra input.

## Converting ordinary diagrams

For `D : J ⥤ EtaleDerivedSections.ModuleSheaf X R`, `ofFixed X R J D`
is a `CoefficientDiagram R (fixedSchemeDiagram X J)`. Its object at `i`
is `D.obj i`; its coefficient map on `a : i ⟶ j` is

```text
u.hom.app (D.obj i) ≫ D.map a.
```

The identity law follows from the identity law of `D` and the restriction
identity above. The composition law follows from the coherence identity,
the naturality of `u`, and the composition law of `D`.

For an ordinary natural transformation `α : D ⟶ E`,
`ofFixedMap X R J α` has component `α.app i` at `i`. Its compatibility
with the new coefficient maps follows from the naturality of `α` and
`u`. Pointwise identities and composition then give the functor

```text
ofFixedFunctor X R J :
  (J ⥤ EtaleDerivedSections.ModuleSheaf X R) ⥤
    CoefficientDiagram R (fixedSchemeDiagram X J).
```

This module constructs this functor and the cohomology comparison; it
does not assert an equivalence between the two coefficient categories.

## Agreement of the cohomology constructions

`ofFixed_cohomology_map` proves, for every `q : ℕ` and `a : i ⟶ j`,

```text
((ofFixed X R J D).cohomology q).map a =
  (EtaleDerivedSections.cohomology X R q).map (D.map a).
```

The left side is constructed as derived pullback along the identity
scheme map followed by cohomology of the coefficient map. Expanding that
map, the proof uses `EtalePullback.cohomologyMap_id` to cancel identity
pullback against cohomology of `u`. This leaves exactly the right side.
The objects on both sides are already definitionally the same actual
right-derived global-section modules.

Consequently `ofFixedCohomologyIso X R J D q` is a natural isomorphism
with identity components:

```text
(ofFixed X R J D).cohomology q ≅
  D ⋙ EtaleDerivedSections.cohomology X R q.
```

Its naturality is the proved arrow formula. Finally,
`ofFixedCohomologyFunctorIso X R J q` gives the comparison at the level
of coefficient-diagram functors:

```text
ofFixedFunctor X R J ⋙ cohomologyFunctor q ≅
  EtaleDerivedSections.diagramFunctor X R J q.
```

Naturality in coefficient morphisms holds because both constructions act
at each vertex by cohomology of the same sheaf map, and the comparison
components are identities.

## Provenance and use with existing coefficient systems

The construction is internal infrastructure derived from the existing
restriction identifications, their actual presheaf formulas, and the
proved identity law for derived pullback. No named literature theorem
or new geometric existence claim is made.

In particular, with `J := ℕᵒᵖ`, the ordinary sheaf diagrams produced by
`EtaleAdicSystem.functor X I` or
`EtaleAdicSystem.constantSystemFunctor X I` can be supplied to
`ofFixedFunctor X R J`. The comparison above applies to each such
diagram, so their existing fixed-scheme cohomology diagrams can be used
through the varying-scheme coefficient interface. This follows by
specializing the arbitrary category and diagram parameters; those
coefficient-system constructors are not reimplemented here.

The result concerns a fixed scalar ring, ordinary small-étale
cohomology, and a constant scheme diagram. It constructs no derived
inverse limit, compact support, scalar-change comparison, or actual
Shimura tower. The varying-scheme Harris application still needs the
geometric tower and its compatible sheaf maps.
