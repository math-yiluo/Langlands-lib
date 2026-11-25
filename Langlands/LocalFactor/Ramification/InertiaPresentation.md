# Actual finite inertia restrictions and Weil representation presentations

The construction was first written for p-adic fields and is generalized
in place using the published characteristic-free finite ramification,
absolute inertia, and local Weil group. The field and representation-carrier
universes remain independent.

## Local fields and finite integer rings

For a nonarchimedean local field `K` and a specified separable closure `Ω`,
`Langlands.Ramification.Local.SepClosed` takes Mathlib's `Field`,
`ValuativeRel`, `TopologicalSpace` and `IsNonarchimedeanLocalField` on `K`,
and `Field`, `Algebra K Ω` and `IsSepClosure K Ω` on `Ω`. Its
`finiteTopologicalData K Ω L` for a finite Galois subextension `L` is the
published `localTopologicalData K L`. Its `finiteBaseEmbedding` uses the
actual algebra map from `K` to `L`.

The shared declarations in `Langlands.Ramification.Local` allow a common
spectral base `K₀` as in `Herbrand.GeneralAbsolute`. In this form `K` is
finite over `K₀` and `K₀` has a complete nontrivial ultrametric norm, is
locally compact, and has a valuative relation agreeing with the norm
comparison (`hbase`). The finite integer rings use that spectral norm on
`L`. For maps to the closure, `hK` identifies the `K₀`-spectral unit ball on
`K` with the integers of the supplied valuative relation on `K`. The
ordinary local-field entry points take `K₀ = K`. They obtain both
compatibility proofs from the published `LocalGalois.localNormedField`
adapter and the base restriction of the spectral norm.

`finiteClosureIntegerMap` restricts the actual inclusion `L → Ω` to the
integer rings. The proof identifies the closure integer ring with the
`K₀`-spectral unit ball. The integers of `K` are integral over the integers
of `K₀` by the published `integral_iff_mem_spectralIntegers` and `hK`.
The actual tower of integer scalars then identifies integrality over the two
base rings in `Ω`. The spectral norm over `K₀` agrees under `L → Ω` by
`spectralNorm.eq_of_tower`. These facts give preservation and reflection of
integer membership, and `finiteClosureIntegerMap_coe` gives the actual field
inclusion on representatives. At `h : L ≤ M`, `finiteIntegerMap h` similarly
restricts `IntermediateField.inclusion h`, using the spectral norm over `K₀`
on both fields. Both ring inclusions are local homomorphisms. An inverse in
the target integer ring is the image of the inverse in the source field,
and reflection of membership places that inverse in the source integer ring.
Their induced maps of residue fields are injective.

## Inertia restrictions

`absoluteInertiaRestriction` restricts the published continuous
`absoluteFiniteRestriction`, whose field operation is
`AlgEquiv.restrictNormalHom`. Absolute inertia is the actual residue kernel
`LocalGalois.SepClosed.absoluteInertia`. To see that the restriction lands in
finite inertia, lift a residue class in the finite field to an integer and
apply the injective map to the closure residue field. The absolute inertia
condition gives the resulting equality, since the restricted automorphism
and the original automorphism agree on the embedded integer. Continuity is
inherited through the two subgroup topologies. The `_coe` and `_apply`
lemmas give the finite Galois element and its evaluation in `Ω`.

`weilInertiaProjection` restricts the published Weil projection from
`Weil.Local.SepClosed.localInertia` to absolute inertia. A Weil element of
degree zero has trivial profinite residue degree, and the published
`localResidueDegree_ker` identifies this kernel with absolute inertia.
`weilInertiaRestriction` composes the projection with absolute inertia
restriction. Its evaluation is the restriction of the original Weil
projection on the same field element.

`finiteGaloisRestriction h` uses `AlgEquiv.restrictNormalHom` for the algebra
structure from `IntermediateField.inclusion h`. Finite Galois groups have
their discrete Krull topologies. The injective residue map along the finite
integer map proves the residue kernel condition by the same elementwise
argument as for absolute inertia. It gives `finiteInertiaRestriction h`.
`finiteInertiaRestriction_absolute` and `finiteInertiaRestriction_weil` show
that restriction through `M` agrees with restriction directly to `L`.
Consequently the Weil inertia restriction kernel for `M` is contained in
the one for `L`.

## Presentations, conductor sums and refinement

For `A : FiniteRepresentation ℂ (Weil.Local.SepClosed.localWeilGroup K Ω)`,
`localInertiaRepresentation` restricts the actual representation to Weil
inertia on the original carrier. `FiniteInertiaPresentation` specializes the
shared record `FiniteInertiaPresentationData`. Its fields are `extension`, a
finite Galois subextension, and `kernel_le`, asserting that the kernel of Weil
inertia restriction to that extension acts trivially on `A`. Keeping that
condition as a parameter of the underlying record lets its constructor and
projections use the field data directly.

`P.representation hsurj` descends along `weilInertiaRestriction` for
`P.extension` with the supplied surjectivity proof `hsurj` and `P.kernel_le`.
It evaluates on Weil inertia images as the original action. The rational
values `P.artinConductor hsurj` and `P.swanConductor hsurj` use the published
`artinConductorOfQuotient` and `swanConductorOfQuotient`. The Artin sum has a
term for each lower group from index zero, with weight `|Gᵢ| / |G₀|` times
the codimension of its fixed vectors. The Swan sum uses the positive lower
indices. Trivial lower groups give zero terms, so the published termination
bound suffices for the sums. Each value is attached to the supplied
presentation.

`P.refine M h` uses the kernel containment for the inclusion into `M`.
`P.pullback hsurj M h` precomposes the descended action at `P.extension`
with actual finite inertia restriction. Its evaluation on Weil inertia
follows from the restriction square. Descent at `M`, given surjectivity
there, equals this pullback because both agree on every lifted element.

`FiniteInertiaCommonRefinement` specializes `FiniteInertiaCommonRefinementData`
with a common subextension `extension` and inclusions `left_le` and
`right_le`. `compositum` uses the finite Galois compositum of the two
subextensions. `leftRepresentation` and `rightRepresentation` give the two
pullbacks. Their elements agree on images of Weil inertia, so surjectivity at
the common subextension gives `representations_eq`. The existing separate
statement targets address surjectivity, existence of a presentation for a
continuous representation, and independence of the conductor sums.

## Characteristic and p-adic specialization

The former absolute Galois, absolute inertia and Weil objects used
`AlgebraicClosure F.Carrier`, which is separable over the characteristic-zero
base. The general closure `Ω` supplies separability and separable closedness
through `IsSepClosure K Ω` for the corresponding published groups. The
individual finite subextensions already have separability and normality in
`FiniteGaloisIntermediateField`. The former finite fields and their integer
rings were packaged over `Padic p`. The general finite constructor uses
`LocalField.canonicalTopologicalData`, and the integer and residue map proofs
use the scalar tower and spectral integrality in either characteristic.
The representation and descent arguments use only the specified group maps
and complex linear algebra.

The `Langlands.Ramification.Padic` definitions unfold through the shared
spectral construction at `K₀ = Padic p`, `K = F.Carrier` and
`Ω = AlgebraicClosure F.Carrier`. The base is given
`F.canonicalTopologicalData`'s valuative relation and topology, and
`finiteTopologicalData` is the general view of the canonical topological
data of `absoluteFiniteExtension F L`. The specialized record types use the
same shared constructors. The p-adic record applies the named p-adic
restrictions in its kernel condition, so existing constructor syntax
introduces elements of the p-adic Weil inertia type. The p-adic constructor,
projection and eliminator names are available in the original namespaces,
with the original universe order and the original argument names, order and
implicitness. The constructor injectivity lemmas specialize the generated
lemmas of the shared records, preserving their field argument names.
The p-adic finite integer inclusion used in the old residue proof is
`Weil.Local.extensionIntegerMap` at the scalar restriction of
`IntermediateField.inclusion h`.

| Shared `Langlands.Ramification.Local` | P-adic `Langlands.Ramification.Padic` |
| --- | --- |
| `finiteTopologicalData` | `(absoluteFiniteExtension F L).canonicalTopologicalData.toLocalData` |
| `finiteIntegerMap` | `Weil.Local.extensionIntegerMap` on the actual inclusion |
| `finiteBaseEmbedding` | `finiteBaseEmbedding` |
| `finiteClosureIntegerMap` | `finiteClosureIntegerMap` |
| `finiteClosureIntegerMap_coe` | `finiteClosureIntegerMap_coe` |
| `finiteClosureIntegerMap_isLocalHom` | `finiteClosureIntegerMap_isLocalHom` |
| `absoluteFiniteRestriction_mem_inertia` | `absoluteFiniteRestriction_mem_inertia` |
| `absoluteInertiaRestriction` | `absoluteInertiaRestriction` |
| `absoluteInertiaRestriction_coe` | `absoluteInertiaRestriction_coe` |
| `absoluteInertiaRestriction_apply` | `absoluteInertiaRestriction_apply` |
| `weilInertiaProjection` | `weilInertiaProjection` |
| `weilInertiaProjection_coe` | `weilInertiaProjection_coe` |
| `weilInertiaRestriction` | `weilInertiaRestriction` |
| `weilInertiaRestriction_coe` | `weilInertiaRestriction_coe` |
| `weilInertiaRestriction_apply` | `weilInertiaRestriction_apply` |
| `finiteGaloisRestriction` | `finiteGaloisRestriction` |
| `finiteGaloisRestriction_apply` | `finiteGaloisRestriction_apply` |
| `finiteGaloisRestriction_mem_inertia` | `finiteGaloisRestriction_mem_inertia` |
| `finiteInertiaRestriction` | `finiteInertiaRestriction` |
| `finiteInertiaRestriction_coe` | `finiteInertiaRestriction_coe` |
| `finiteInertiaRestriction_absolute` | `finiteInertiaRestriction_absolute` |
| `finiteInertiaRestriction_weil` | `finiteInertiaRestriction_weil` |
| `weilInertiaRestriction_ker_le` | `weilInertiaRestriction_ker_le` |
| `localInertiaRepresentation` | `localInertiaRepresentation` |
| `FiniteInertiaPresentation` | `FiniteInertiaPresentation` |
| `FiniteInertiaPresentationData.mk` | `FiniteInertiaPresentation.mk` |
| `FiniteInertiaPresentationData.extension` | `FiniteInertiaPresentation.extension` |
| `FiniteInertiaPresentationData.kernel_le` | `FiniteInertiaPresentation.kernel_le` |
| `FiniteInertiaPresentationData.rec` | `FiniteInertiaPresentation.rec` |
| `FiniteInertiaPresentationData.recOn` | `FiniteInertiaPresentation.recOn` |
| `FiniteInertiaPresentationData.casesOn` | `FiniteInertiaPresentation.casesOn` |
| `FiniteInertiaPresentationData.ctorIdx` | `FiniteInertiaPresentation.ctorIdx` |
| `FiniteInertiaPresentationData._sizeOf_inst` | `FiniteInertiaPresentation._sizeOf_inst` |
| `FiniteInertiaPresentationData._sizeOf_1` | `FiniteInertiaPresentation._sizeOf_1` |
| `FiniteInertiaPresentationData.mk._flat_ctor` | `FiniteInertiaPresentation.mk._flat_ctor` |
| `FiniteInertiaPresentationData.mk.inj` | `FiniteInertiaPresentation.mk.inj` |
| `FiniteInertiaPresentationData.mk.injEq` | `FiniteInertiaPresentation.mk.injEq` |
| `FiniteInertiaPresentationData.mk.sizeOf_spec` | `FiniteInertiaPresentation.mk.sizeOf_spec` |
| `FiniteInertiaPresentationData.noConfusionType` | `FiniteInertiaPresentation.noConfusionType` |
| `FiniteInertiaPresentationData.noConfusion` | `FiniteInertiaPresentation.noConfusion` |
| `FiniteInertiaPresentationData.mk.noConfusion` | `FiniteInertiaPresentation.mk.noConfusion` |
| `FiniteInertiaPresentation.representation` | `FiniteInertiaPresentation.representation` |
| `FiniteInertiaPresentation.representation_apply` | `FiniteInertiaPresentation.representation_apply` |
| `FiniteInertiaPresentation.artinConductor` | `FiniteInertiaPresentation.artinConductor` |
| `FiniteInertiaPresentation.swanConductor` | `FiniteInertiaPresentation.swanConductor` |
| `FiniteInertiaPresentation.refine` | `FiniteInertiaPresentation.refine` |
| `FiniteInertiaPresentation.pullback` | `FiniteInertiaPresentation.pullback` |
| `FiniteInertiaPresentation.pullback_apply` | `FiniteInertiaPresentation.pullback_apply` |
| `FiniteInertiaPresentation.representation_refine` | `FiniteInertiaPresentation.representation_refine` |
| `FiniteInertiaCommonRefinement` | `FiniteInertiaCommonRefinement` |
| `FiniteInertiaCommonRefinement.compositum` | `FiniteInertiaCommonRefinement.compositum` |
| `FiniteInertiaCommonRefinementData.mk` | `FiniteInertiaCommonRefinement.mk` |
| `FiniteInertiaCommonRefinementData.extension` | `FiniteInertiaCommonRefinement.extension` |
| `FiniteInertiaCommonRefinementData.left_le` | `FiniteInertiaCommonRefinement.left_le` |
| `FiniteInertiaCommonRefinementData.right_le` | `FiniteInertiaCommonRefinement.right_le` |
| `FiniteInertiaCommonRefinementData.rec` | `FiniteInertiaCommonRefinement.rec` |
| `FiniteInertiaCommonRefinementData.recOn` | `FiniteInertiaCommonRefinement.recOn` |
| `FiniteInertiaCommonRefinementData.casesOn` | `FiniteInertiaCommonRefinement.casesOn` |
| `FiniteInertiaCommonRefinementData.ctorIdx` | `FiniteInertiaCommonRefinement.ctorIdx` |
| `FiniteInertiaCommonRefinementData._sizeOf_inst` | `FiniteInertiaCommonRefinement._sizeOf_inst` |
| `FiniteInertiaCommonRefinementData._sizeOf_1` | `FiniteInertiaCommonRefinement._sizeOf_1` |
| `FiniteInertiaCommonRefinementData.mk._flat_ctor` | `FiniteInertiaCommonRefinement.mk._flat_ctor` |
| `FiniteInertiaCommonRefinementData.mk.inj` | `FiniteInertiaCommonRefinement.mk.inj` |
| `FiniteInertiaCommonRefinementData.mk.injEq` | `FiniteInertiaCommonRefinement.mk.injEq` |
| `FiniteInertiaCommonRefinementData.mk.sizeOf_spec` | `FiniteInertiaCommonRefinement.mk.sizeOf_spec` |
| `FiniteInertiaCommonRefinementData.noConfusionType` | `FiniteInertiaCommonRefinement.noConfusionType` |
| `FiniteInertiaCommonRefinementData.noConfusion` | `FiniteInertiaCommonRefinement.noConfusion` |
| `FiniteInertiaCommonRefinementData.mk.noConfusion` | `FiniteInertiaCommonRefinement.mk.noConfusion` |
| `FiniteInertiaCommonRefinement.leftRepresentation` | `FiniteInertiaCommonRefinement.leftRepresentation` |
| `FiniteInertiaCommonRefinement.rightRepresentation` | `FiniteInertiaCommonRefinement.rightRepresentation` |
| `FiniteInertiaCommonRefinement.leftRepresentation_apply` | `FiniteInertiaCommonRefinement.leftRepresentation_apply` |
| `FiniteInertiaCommonRefinement.rightRepresentation_apply` | `FiniteInertiaCommonRefinement.rightRepresentation_apply` |
| `FiniteInertiaCommonRefinement.representations_eq` | `FiniteInertiaCommonRefinement.representations_eq` |

## Sources and provenance

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
GTM 67 (1979), Chapter IV, §1, Lemma 1 and Proposition 1, printed pp. 61–62
(retained PDF pp. 68–69), describes the integer-ring filtration and its
zeroth group. Section 3, printed pp. 73–75 (PDF pp. 80–82), describes finite
and absolute upper numbering. Chapter VI, §2, printed pp. 99–101
(PDF pp. 106–108), especially Proposition 2 and Corollary 1′, gives the
weighted fixed-space codimension formula for conductors. The registered
source is `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

Pierre Deligne and Guy Henniart, *Sur la variation, par torsion, des constantes
locales d'équations fonctionnelles de fonctions L* (1981), §0.5, printed p. 92
(PDF p. 4), specifies continuous finite-dimensional complex representations
of the Weil group and finite image on inertia. The registered source is
`deligne-henniart-1981-variation`, SHA256
`54fe3348af12263a8d3774a0353fff352cb041728f446fb0cccc4b0f97803a3e`.
The explicit Lean restriction maps, kernel fields and refinements are
internal constructions on the supplied arithmetic objects. They reuse the
published finite and absolute ramification, Weil assembly and descent APIs.
