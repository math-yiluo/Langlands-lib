# Full coefficient-cover diagrams on the exact geometric CM levels

This module constructs the full geometric coefficient-cover diagram at the
original Harris coefficient kernel levels. It identifies that diagram,
including every transition and residual action, with the geometric pullback of
the published original coefficient-cover diagram.

The construction is conditional on the same exact representability and named
geometric prerequisites as the published geometric normal torsors. The desired
diagram or its comparison is not an input.

## Inputs and exact objects

The number fields `E`, `F`, `L`, central simple unitary datum `D`, signature
charts `C`, and all tensor, Picard-zero, duality, polarization, Weil-transition,
adelic-comparison and torsion-finiteness inputs are those of the imported CM
scheme tower. All arithmetic types and schemes here are in universe zero.

`q : CMRepresentabilityStatement ...` supplies the exact representation
existence assertion for the constructed CM class presheaves. The same
`chosenCMLevelRepresentation ... q` is used by the original scheme tower and
its geometric base change. The module retains this existence premise; it does
not prove it or choose unconstrained output schemes.

Fix a small original level `U`, a finite-dimensional algebraic representation
`ρ` over a number field `K`, a finite place `p` of the rationals, and
`m : ℕ` with `hm : m ≠ 0`. The index category is the actual opposite natural
number category. At index `k`, write

\[
 V_k=\operatorname{cmHarrisCoefficientLevel}(D,ρ,p,U,m,hm,k),
 \qquad G_k=U/(V_k\text{ as a subgroup of }U).
\]

These are the already constructed full coefficient kernels, including all
coefficient powers and the original opposite-group convention. Their actual
inclusions give `cmHarrisCoefficientLevels`; their identity-induced residual
quotient homomorphisms give `cmHarrisCoefficientGroups`. The construction uses
these functors without modification. The coefficient field, lattice, integral
scalars and full torsion quotients remain those of the published original
coefficient system.

Write `X(V)` for the original scheme tower, `Xbar(V)` for
`cmGeometricSchemeTower ... q`, and `π_V : Xbar(V) ⟶ X(V)` for
`cmGeometricProjection ... q`. Thus `Xbar(V)` is the existing scheme fiber
product with `Spec (AlgebraicClosure F)` along the original `F` structure.

The small-etale objects and torsor results additionally retain
`RelativeDualSchemeExistenceStatement`, `RelativeDualSchemeGeometryStatement`,
and the original `CMGeometricCoarseRigidity ... U.obj` premise. The generic
dominant-unramified-etale criterion is discharged by
`DominantUnramifiedEtaleProof.dominantUnramifiedEtale`. The other retained
premises are not discharged by this contribution.

## Geometric schemes, projections and torsors

`cmHarrisGeometricCoefficientSchemeDiagram` is an `EquivariantDiagram` over the
original residual group functor. Its underlying functor is literally

```lean
cmHarrisCoefficientLevels D ρ p U m hm ⋙ cmGeometricSchemeTower ... q
```

Its action at `k` is the existing `cmGeometricNormalQuotientAction` for
`U` and `V_k`. A representative `g` acts by the existing geometric tower map at
`smallCMNormalInverseArrow ... g`, preserving the inverse-right normalization.
Transition equivariance is proved by residual quotient induction. On a
representative, functoriality reduces it to the published equality
`smallCMNormalInverseArrow_inclusion` of the actual level arrows.

`cmHarrisGeometricCoefficientSchemeProjection` projects the diagram to the
constant scheme `Xbar(U)` by the exact coarse forgetting maps. Its naturality
uses composition of the original inclusion arrows and functoriality of the
geometric scheme tower. Its invariance theorem specializes the existing
geometric normal projection invariance to each `V_k`.

`cmHarrisGeometricCoefficientTorsor k` specializes the published
`cmGeometricNormalGeometricTorsor_of_dominantCriterion` to precisely this
coefficient level. It returns the existing action in `Xbar(U).Etale` together
with its proved `IsFiniteGeometricTorsor` property. In particular, the residual
group is finite, the structural morphism is finite and surjective, and any two
points over a separably closed field with the same coarse image have a unique
residual translator. Etaleness is part of the ambient object. These are the
existing predicate's geometric-point quantifiers, without an assertion of a
single constant translator over arbitrary disconnected test schemes.

`cmHarrisGeometricCoefficientEtaleTower` bundles these exact sources and
structural morphisms in the small-etale category of `Xbar(U)`. Its maps have
exactly the geometric scheme forgetting maps as their underlying scheme maps.
Projection naturality proves that they are morphisms over this same coarse
scheme; slice extensionality and scheme-tower functoriality prove the functor
laws.

`cmHarrisGeometricCoefficientEtaleDiagram` bundles the same actions over the
same group functor. Slice extensionality reduces its transition equivariance
to that already proved for the geometric scheme diagram. The `_action`,
`_obj_left`, `_obj_hom`, `_map_left` and `_action_mk_left` lemmas identify its
exact components, structural maps, transitions and representative deck maps.
The `_isFiniteGeometricTorsor` result uses the property of the constructed
torsor, and `_coversTop` applies the published surjective-etale-cover result.
Thus every displayed component covers the final object of the actual
small-etale site.

## Canonical comparison of complete diagrams

Let `Y` be the existing `cmHarrisCoefficientEtaleDiagram` over `X(U)` and the
same residual group functor `G`. The comparison target is exactly

```lean
(etaleTorsorDiagramPullback π_U G).obj Y
```

This is the published generic pullback functor on varying-group cover diagrams.
It allows an arbitrary base morphism. No etaleness of `π_U` is assumed.

At each index, `cmHarrisGeometricCoefficientEtaleActionPullbackIso` is the
already published `cmGeometricNormalEtaleActionPullbackIso` specialized to
`V_k` and the discharged dominant criterion. Its underlying map is the
canonical isomorphism of the existing cartesian square

\[
 Xbar(V_k)\simeq X(V_k)\times_{X(U)}Xbar(U).
\]

`cmHarrisGeometricCoefficientEtaleTowerPullbackIso` makes these component
isomorphisms into a natural isomorphism. The proof checks both projections of
the target fiber product. On the original fine-level coordinate, the
pullback-lift projection equation reduces the claim to naturality of
`cmGeometricProjection` at the exact original transition arrow. On the coarse
geometric coordinate, the second pullback-lift equation reduces it to
naturality of `cmHarrisGeometricCoefficientSchemeProjection`. This proves
compatibility with every actual coefficient-level transition.

The entry definition `cmHarrisGeometricCoefficientEtaleDiagramPullbackIso`
bundles this natural isomorphism as an isomorphism of full equivariant diagrams.
Its forward and inverse equivariance fields are exactly those of the published
component action isomorphisms. Its inverse laws follow from the underlying
natural isomorphism and extensionality of equivariant-diagram morphisms.

The final `_hom_app_left` and `_inv_app_left` lemmas identify the underlying
maps with the same `isoPullback.hom` and `isoPullback.inv` of the original
cartesian square, by reflexivity. The `_hom_app_fst` and `_hom_app_snd` lemmas
identify the coordinates with `π_{V_k}` and the exact coarse geometric
forgetting map. No replacement cartesian comparison is selected.

## Provenance and remaining scope

This is an internal deduction from published constructions:
`HarrisTaylorCMCoefficientDiagram`, `HarrisTaylorCMCoefficientSchemes`,
`HarrisTaylorCMGeometricNormalActions`, `HarrisTaylorCMGeometricNormalTorsor`
and `Coefficients.EtaleTorsorPullback`, together with the original level-arrow
identity in `HarrisTaylorCMNormalRefinement`. The new result assembles their
exact objects into a compatible diagram and proves naturality of their
canonical component comparisons. It introduces no additional assertion from
external literature; the original-source provenance of the reused moduli,
coefficient kernels and geometric normal torsors remains in their paired
modules.

The full exact representability theorem, source-moduli rigidity and comparison,
canonical-model geometry and the other named premises remain obligations.
This contribution does not identify associated coefficient sheaves under
arbitrary inverse image, prove the corresponding coefficient descent, or
complete the host task. It supplies the exact geometric cover diagram and its
canonical equivariant comparison for those subsequent constructions.
