# Coefficient transport under a change of index category

This internal construction connects the geometric and restriction coefficient
categories with their existing reindexing operations. It proves that both
transport functors commute with reindexing and that the already constructed
derived, ordinary-cohomology and section comparisons themselves precompose.

The inputs are a commutative ring `R : Type u`, an index category `J : Type v`
with morphisms in `Type w`, a functor `S : J ⥤ Scheme.{u}ᵒᵖ`, and a functor
`F : K ⥤ J`, where `K` has independent object and morphism universes `v'` and
`w'`. Every scheme map `(S.map a).unop` is etale. The coefficient objects are
actual small-etale sheaves valued in `ModuleCat.{u} R`. Coefficient transition
maps need not be isomorphisms. No field, finiteness or local-constancy hypothesis
is imposed.

The transport and round-trip declarations require no derived-category
hypotheses. All declarations involving cohomological diagrams retain a common
vertex-sheaf localization universe `wS` and an independent module-localization
universe `wR`. Reindexed vertices reuse the original sheaf-localization instance
at `F.obj i`. Ordinary degrees are `q : ℕ`.

## The coefficient categories

Use `G(S)` for geometric coefficient diagrams and `T(S)` for restriction
coefficient diagrams. Let `U : T(S) ⥤ G(S)` be `ofRestrictionFunctor` and
`V : G(S) ⥤ T(S)` be `toRestrictionFunctor`. Let `rG` and `rT` denote
reindexing along `F`. The new natural isomorphisms have directions

```text
reindexOfRestrictionIso : rT ⋙ U ≅ U ⋙ rG
reindexToRestrictionIso : rG ⋙ V ≅ V ⋙ rT.
```

Here the transport on the left is formed over `F ⋙ S`, and the transport on the
right is formed over `S`. Both orders preserve the same vertex sheaf
`D.obj (F.obj i)` and component sheaf morphism. The geometric transition in
either order is the canonical inverse-image/restriction comparison along
`S.map (F.map a)`, followed by `D.map (F.map a)`. The reverse transition uses the
inverse of that same comparison. Thus both isomorphisms are `Iso.refl`, with
identity coefficient components; the corresponding object equalities are
`reindex_ofRestriction` and `reindex_toRestriction`.

`reindex_geometricRoundTripIso` and `reindex_restrictionRoundTripIso` identify
the specified round-trip isomorphisms at reindexed coefficients with the
reindexing functor applied to the original isomorphism. This preserves the
existing chosen isomorphisms, including both hom and inverse maps. After
isomorphism and coefficient-morphism extensionality, both components are the
identity sheaf morphism at `F.obj i`.

## Actual cohomological diagrams

The small restriction-side API in
`EtalePullback.CoefficientDiagram` supplies `reindex_derivedSections`,
`reindexDerivedSectionsIso` and `reindexDerivedSectionsFunctorIso`. The actual
restriction-derived diagram at reindexed coefficients is definitionally
`F ⋙ D.derivedSections`. Its comparison has identity vertex maps and is natural
in compatible coefficients: both coefficient maps apply the actual derived
section functor to `α.app (F.obj i)`. This extends the ordinary-cohomology and
section reindexing API already in `EtaleCohomologyReindex`.

In `EtaleGeometricDiagram.CoefficientDiagram`, the six theorems

```text
reindex_ofRestrictionDerivedSectionsIso
reindex_ofRestrictionCohomologyIso
reindex_ofRestrictionSectionsIso
reindex_toRestrictionDerivedSectionsIso
reindex_toRestrictionCohomologyIso
reindex_toRestrictionSectionsIso
```

identify the existing comparison at reindexed coefficients with
`Functor.isoWhiskerLeft F` of the original comparison. The source and target
diagrams agree definitionally by the coefficient interchange and the component
formulas for reindexing. The forward comparison has the same identity
component at the same vertex sheaf. The reverse comparison is the existing
inverse-forward comparison followed by the functorial image of the specified
round trip; reindexing selects the same composite at `F.obj i`. Isomorphism and
natural-transformation extensionality therefore prove equality of the full
isomorphisms.

Four theorems ending in `FunctorIso` express explicit squares on the entire
appropriate coefficient category: the forward derived-section square and the
reverse derived-section, ordinary-cohomology and section squares. These retain
the coefficient interchange and the two reindex comparison edges. For the
forward derived square, write `C : U ⋙ DG ≅ DT` for the existing comparison,
`bT : rT ⋙ DT ≅ DT ⋙ P` and `bG : rG ⋙ DG ≅ DG ⋙ P` for derived reindexing,
and `a : rT ⋙ U ≅ U ⋙ rG` for coefficient interchange. The equation is

```text
isoWhiskerLeft rT C ≪≫ bT
  =
isoWhiskerRight a DG ≪≫ isoWhiskerLeft U bG ≪≫ isoWhiskerRight C P.
```

Here `P` is precomposition by `F`; each occurrence of `U`, `DG` or `DT`
is over its indicated index category. For reverse transport, replace `U` by
`V`, exchange geometric and restriction diagrams, and use
`reindexToRestrictionIso`. The reverse equations use derived sections,
ordinary cohomology in each degree `q`, and actual sections respectively.
The equalities compare the specified natural isomorphisms, including their
inverse maps. No newly chosen comparison replaces an existing one.

Each proof applies isomorphism and natural-transformation extensionality,
first in the coefficient diagram and then at a vertex. The forward equation
reduces to identities and a functor applied to an identity. In the reverse
case the component formula from `EtaleCoefficientComparisonRecovery` gives
the same specified round-trip map at the reindexed vertex on each side;
functor identity and categorical identity laws finish the proof. Thus the
square holds naturally in arbitrary compatible coefficient morphisms.
The forward ordinary-cohomology and section conclusions in this module are
the full diagram-isomorphism reindexing laws listed above; separate equations
of their coefficient-functor squares are not asserted here.

## Provenance and scope

This is a derived internal categorical construction. Its inputs are the actual
coefficient transports and round trips from `EtaleCoefficientEquivalence`,
the actual geometric reindexing from `EtaleGeometricCoefficientReindex`,
restriction reindexing from `EtaleCohomologyReindex`, and both directions of the
existing comparisons from `EtaleCoefficientDiagramComparison` and
`EtaleCoefficientComparisonRecovery`. The objects are the existing small-etale
module sheaves, geometric inverse images, global sections and right-derived
global sections. The proofs use unchanged component formulas,
extensionality and categorical identity laws. No comparison, interchange law or desired cohomology object is
an input.

This pair does not construct tower limits, compact supports, smooth or Galois
actions, scalar change, arithmetic coefficients or a particular Harris tower.
The required geometric and arithmetic specialization remains separate work.
