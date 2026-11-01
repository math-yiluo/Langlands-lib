# The original CM normal action as a finite geometric torsor

This module combines the existing projective finiteness theorem and the
proved surjectivity of original represented CM transitions. It derives the
existing finite geometric torsor predicate for the original normal-level
small etale action, then packages that action with the proof. The explicit
geometric inputs are etaleness of original forgetting, invertibility of
its exact residual kernel-pair comparison, and the two named relative dual
assertions. Exact CM representability and all inherited prerequisites
remain inputs.

## Original levels, projection and action

Fix a family `R` of the existing `CMLevelRepresentation` witnesses and
small levels `V ≤ U`, where `V` is normal inside `U`. Write

```
X_U = (representedCMSchemeTower ... R).obj U,
X_V = (representedCMSchemeTower ... R).obj V,
p = representedCMNormalProjection ... R U V hVU : X_V ⟶ X_U,
Q = SmallCMResidualGroup D U V.
```

Each representation is an actual admissible scheme over `Spec F`, with
smoothness, a projective-space closed immersion and a natural isomorphism
from lifted Yoneda to the fixed normalized CM class presheaf. The tower
maps are recovered from that isomorphism by fully faithful Yoneda. The
projection `p` is exactly the map at `smallCMInclusion D hVU`.
The residual group is
`U.obj.subgroup ⧸ V.obj.subgroup.subgroupOf U.obj.subgroup`; the denominator
is the given subgroup of `U`, without requiring normality in the entire
finite adelic group.

The action is precisely `representedCMNormalEtaleAction ... R U V hVU`
from `HarrisTaylorCMNormalEtale`, an action of `Q` in `X_U.Etale` under
`Etale p`. Its object has source `X_V` and structural map `p`. Its maps are
the original `representedCMNormalQuotientAction` maps, using the proved
invariance equation over `X_U`. The inverse-right convention is preserved:
a representative `g` acts through the original transporter for `g⁻¹`,
converting right frame composition to Mathlib's left categorical action
in the existing opposite finite adelic group.

Let `κ` be the exact existing `representedCMNormalKernelComparison`.
It maps the actual scheme coproduct of copies of `X_V`, indexed by `Q`,
to the actual self-pullback of `p`. On summand `g` its first projection
is identity and its second is the original residual action map.
The hypothesis `IsIso κ` concerns this particular comparison.

## The reduced-premise torsor theorem

`representedCMNormalEtaleAction_isFiniteGeometricTorsor_of_dualGeometry`
takes the following additional premises:

- `existence : RelativeDualSchemeExistenceStatement.{0}`;
- `geometry : RelativeDualSchemeGeometryStatement.{0}`;
- `Etale p`;
- `IsIso κ`.

The first named proposition gives an actual universal Picard-zero dual
scheme for every abelian scheme over a quasi-separated base. The second
gives smoothness, properness and geometric connectedness of the actual
dual scheme, for every such dual witness. They are substantive named
assertions; neither supplies a CM lift or transporter surjectivity.

The conclusion is exactly

```
Coefficients.IsFiniteGeometricTorsor X_U
  (representedCMNormalEtaleAction ... R U V hVU).
```

This existing predicate, in `Shimura/Coefficients/Etale`, requires a finite
acting group, a finite and scheme-surjective structural map, and unique
residual translation for every pair of separably closed field-valued
points with the same projection. Etaleness is already part of the action
object's small etale category.

The implemented proof applies
`representedCMNormalEtaleAction_isFiniteGeometricTorsor_of_projective`
from `HarrisTaylorCMFiniteEtale`. That theorem obtains finiteness of `p`
from the actual projective embeddings and etaleness: each level's
structure map is proper, the tower equation over `Spec F` proves
properness of the transition, and etaleness gives local quasi-finiteness.
Mathlib's proper-plus-locally-quasi-finite theorem proves finiteness.
The normal-action adapter already proves finiteness of `Q` and obtains
unique field-valued transport from `IsIso κ` by factoring a field spectrum
through a unique summand of the coproduct.

The only remaining argument of that adapter is scheme surjectivity.
Here it is discharged by `representedCMSchemeTower_map_surjective` from
`HarrisTaylorCMSchemeSurjectivity`, applied to `smallCMInclusion D hVU`
and the two named relative dual assertions. The preceding module proves
this result by lifting invariant frame classes at identity geometric
points on the same polarized representative, preserving its joint
determinant and numerical witnesses. Existing natural evaluation
isomorphisms transfer those lifts to the disconnected presheaf. The named
dual assertions admit the actual field tests to the restricted category;
the exact representing isomorphisms convert their class lifts to actual
morphisms. Algebraic closures of residue fields detect surjectivity on
scheme points. The present proof uses that theorem on the original `p`.
Thus neither finiteness nor scheme surjectivity is an extra premise here.

## Constructed values and their identifications

`representedCMNormalGeometricTorsor` returns the direct subtype

```
{Y : Action X_U.Etale Q // Coefficients.IsFiniteGeometricTorsor X_U Y}.
```

Its value is the existing original small etale action and its property
is the new theorem. It takes no arbitrary action or torsor proof as an
input. It uses the existing predicate without introducing a competing
notion of geometric torsor.

Four definitional identifications expose this construction:

- `representedCMNormalGeometricTorsor_val` identifies its value with
  `representedCMNormalEtaleAction`;
- `representedCMNormalGeometricTorsor_left` identifies the source with `X_V`;
- `representedCMNormalGeometricTorsor_hom` identifies the structural map with `p`;
- `representedCMNormalGeometricTorsor_ρ_left` identifies each underlying
  action map with the original inverse-right residual translation.

For `q : CMRepresentabilityStatement ...`,
`cmNormalEtaleAction_isFiniteGeometricTorsor_of_dualGeometry` specializes
the theorem to `chosenCMLevelRepresentation ... q`. These are the
identical chosen witnesses used to define the existing `cmSchemeTower`.
The entry `cmNormalGeometricTorsor` constructs the subtype value over that
tower's actual coarse scheme, and `cmNormalGeometricTorsor_val` identifies
its action with the existing `cmNormalEtaleAction`. The choices come from
the precise representability proposition and do not prove that proposition.

## Original source and retained scope

The source is Harris and Taylor, *The Geometry and Cohomology of Some
Simple Shimura Varieties* (2001), III.1, printed pp.90–91, especially p.91,
one-based PDF pp.98–99. It is registered as
`harris-taylor-2001-geometry-cohomology-simple-shimura`, with SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The passage specifies the connected-component product, the polarized
moduli classes with invariant pairing-compatible adelic frame orbits,
and right frame-composition transitions. It states smooth projective
representability, finite etale forgetting and the normal-level Galois
cover assertion with group `U/V`. This module is a derived adapter from
the preceding concrete constructions and conditional geometry results to
the existing torsor input for coefficient constructions. Its proof route
is the combination described above, rather than a proof attributed
verbatim to the book. All five pages of the supplied author *Publication
with errata* list were read; no entry corrects this cited passage. This
observation is limited to that supplied list.

The arithmetic parameters remain the totally real field `E`, CM field
`F` quadratic over `E`, central simple unitary datum `D`, imaginary
quadratic field `L` inside `F`, embedding `τ₀` and CM-compatible Harris
signature charts `C`. The explicit inherited prerequisites are tensor
pullback preservation, composition, unit coherence, associativity, unitor
comparison and symmetry; Picard-zero pullback stability, Mumford-square
and universal base change; duality naturality, polarization base change,
relative finite Weil transition, the rational profinite-integer/adele
comparison and torsion finite etaleness. The two named relative dual
assertions are additional explicit inputs to this adapter.

The representing witnesses still belong to the existing
`ComponentwiseAdmissibleCMBaseCategory` over `Spec F`; the represented test
category has not been extended. Applicable existence under the source's
division and global hypotheses and comparison with its full moduli problem
remain obligations. Etaleness of the original `p` and invertibility of
the exact `κ` remain hypotheses. The module proves the stated conditional
torsor result; it does not establish the unconditional source cover
theorem, canonical-model comparison, uniformization, coefficient local
systems or their descent comparison, or completion of the host task.

All code and prose in this pair are by Worker 57. The pinned environment
is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
