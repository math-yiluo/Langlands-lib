# Original CM finite-etale projections from the dominant criterion

Author: Worker 57.

This derived construction applies the arbitrary-field component reduction
to the original represented Harris CM normal forgetting map over its
original CM field. It constructs that map as an object of the existing
finite-etale cover category under explicit named prerequisites. It assumes
neither flatness nor etaleness of the original projection.

## Original map and explicit inputs

Fix the existing arithmetic data and a family `R` of exact
`CMLevelRepresentation` witnesses. For small levels `V ≤ U`, with `V`
normal inside `U`, write

```text
X_U = (representedCMSchemeTower ... R).obj U
X_V = (representedCMSchemeTower ... R).obj V
p   = representedCMNormalProjection ... R U V hVU : X_V ⟶ X_U
```

Normality is the hypothesis
`(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal`; it is not normality
in the whole finite adelic group. Each representing witness is an actual
admissible scheme over `Spec F`, with smoothness, a projective embedding and
the exact natural representing isomorphism for the fixed CM class presheaf.
The original tower map is recovered from these isomorphisms by Yoneda.

The additional explicit inputs are
`RelativeDualSchemeExistenceStatement.{0}`,
`RelativeDualSchemeGeometryStatement.{0}`,
`CMGeometricCoarseRigidity ... U.obj` and
`DominantUnramifiedEtaleStatement.{0}`. The first two give existence and
geometric properties of actual universal Picard-zero dual schemes. Coarse
rigidity is the existing geometric CM class-automorphism assertion; it is
not inferred from the type `SmallCMLevel`. The final proposition is the
separate generic integral-source dominant-unramified criterion.

The arithmetic parameters and inherited inputs remain explicit: totally
real `E`, CM `F` quadratic over `E`, central simple unitary datum `D`,
imaginary quadratic `L` inside `F`, embedding `τ₀`, CM-compatible signature
charts `C`; tensor-pullback preservation, composition, unit coherence,
associativity, unitor comparison and symmetry; Picard-zero pullback,
Mumford square and universal base change; duality naturality, polarization
base change, relative finite Weil transition, the rational
profinite-integer/adele comparison and torsion finite etaleness.

## Implemented deduction and constructed cover

`representedCMNormalProjection_etale_of_dominantCriterion` installs
smoothness of the original fine and coarse structure maps directly from
`(R V).smooth` and `(R U).smooth`. Original properness supplies local finite
type. The published
`representedCMNormalProjection_formallyUnramified_of_dualGeometry` uses the
original diagonal open immersion to provide formal unramifiedness.
`representedCMNormalProjection_isOpenMap` provides openness using the
original residual action and quotient topology.

The imported `openUnramifiedSmooth_etale_of_dominantCriterion` restricts
this same map to actual integral smooth component schemes, proves
geometric unibranchness of the target components from their normal stalks,
and proves dominance from openness. The supplied generic criterion gives
component etaleness, which the actual source component open cover transfers
to `Etale p`.

`representedCMNormalFiniteEtale_of_dominantCriterion` installs this proved
etaleness and applies the existing `cover` constructor to `p`. The existing
proper-plus-locally-quasi-finite instance supplies finiteness, with local
quasi-finiteness following from the now derived etaleness. Thus the result
is an actual `FiniteEtale.Cover X_U`. Its `_left` and `_hom` theorems identify
its source with `X_V` and its structural map with `p`, both by `rfl`.

The chosen versions `cmNormalProjection_etale_of_dominantCriterion` and
`cmNormalFiniteEtale_of_dominantCriterion` use precisely
`chosenCMLevelRepresentation ... q`, the witnesses defining
`cmSchemeTower ... q`. The latter is the entry construction. Its map is the
direct original map at `smallCMInclusion D hVU`, and its source and map
identifications again hold by `rfl`. The witness
`q : CMRepresentabilityStatement ...` remains an input.

## Original source and retained scope

The source is Harris and Taylor, *The Geometry and Cohomology of Some
Simple Shimura Varieties* (2001), III.1, printed pp.90–91, especially p.91,
one-based PDF pp.98–99. It is registered as
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The passage specifies the componentwise polarized CM frame-orbit moduli,
right frame-composition transitions, smooth projective representability,
finite-etale forgetting and the normal `U/V` Galois-cover assertion. All five
pages of the supplied author *Publication with errata* list were read;
no entry corrects this cited passage. This observation concerns that list.

The implemented route is an internal deduction from the imported
original-map results and the explicit generic criterion, rather than a
proof attributed verbatim to the book. The represented test category remains
`ComponentwiseAdmissibleCMBaseCategory` over the original `Spec F`.
Applicable representability under the source's division and global
hypotheses, the two dual assertions, source rigidity, a proof of the generic
criterion, full moduli comparison, canonical-model geometry and coefficient
descent remain obligations. The present result supplies this conditional
cover on the identical original map.

All code and prose in this pair are by Worker 57. The pinned environment
is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
