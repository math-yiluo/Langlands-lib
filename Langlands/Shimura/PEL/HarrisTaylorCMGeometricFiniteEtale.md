# Finite-etale normal covers on the actual geometric CM tower

Author: Worker 57.

This derived construction proves that every existing geometric CM tower map is
the base change of its original represented tower map. For a normal inclusion
of small levels, it derives finite etaleness of that same geometric map from the
published original finite-etale cover under its explicit named prerequisites.
It packages the actual geometric fine level as a cover and constructs its
canonical comparison with the pulled-back original cover.

## Fixed towers and retained inputs

Fix the original arithmetic data: totally real `E`, CM `F` quadratic over `E`,
central simple unitary datum `D`, imaginary quadratic `L` inside `F`, embedding
`τ₀`, and CM-compatible signature charts `C`. The inherited tensor-pullback
preservation, composition, unit coherence, associativity, unitor comparison and
symmetry; Picard-zero pullback, Mumford square and universal base change;
duality naturality, polarization base change, relative finite Weil transition,
rational profinite-integer/adele comparison and torsion finite-etaleness
propositions remain explicit parameters. So does the exact proposition
`q : CMRepresentabilityStatement ...`.

Use the identical `chosenCMLevelRepresentation ... q` witnesses and the existing
`cmSchemeTower ... q`. Write `X_U` for its level U. The existing
`cmGeometricSchemeTower ... q` has level `Xbar_U`, and
`π_U = (cmGeometricProjection ... q).app U`. These are the actual scheme fiber
products with `Spec (AlgebraicClosure F)` over the original `Spec F`, with the
original `cmGeometricFieldMap`; the construction introduces no new representing
schemes or alternative geometric levels.

## Cartesian level maps

For every level arrow `k : V ⟶ U`,
`cmGeometricSchemeTower_map_isPullback` proves

```text
Xbar_V --- π_V ---> X_V
  |                 |
  | geometric k     | original k
  v                 v
Xbar_U --- π_U ---> X_U.
```

The displayed square is `IsPullback π_V (geometricSchemes.map k)
(schemes.map k) π_U`. Its commutativity is the symmetric naturality equation
of the existing projection. To prove its universal property, the implementation
uses `IsPullback.of_bot` to cancel the known level-U field-base-change square.
The outer square is the known level-V square: both vertical composites reduce
to the respective V structure morphisms by `Over.w`.
No normality or additional dual-geometry or rigidity input is used for this
all-level-map theorem.

## The same geometric normal map as a finite-etale cover

Now fix `hVU : V.obj.subgroup ≤ U.obj.subgroup` and the normality instance
`(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal`. Normality is inside U,
not in the whole finite adelic group. Retain the original cover's additional
inputs: `RelativeDualSchemeExistenceStatement.{0}`,
`RelativeDualSchemeGeometryStatement.{0}`, the exact coarse-level
`CMGeometricCoarseRigidity ... U.obj`, and
`DominantUnramifiedEtaleStatement.{0}`. The last is the named generic
integral-source dominant-unramified criterion. None is proved by this module.

`cmGeometricNormalProjection_etale_of_dominantCriterion` and
`cmGeometricNormalProjection_isFinite_of_dominantCriterion` apply stability
under base change to the preceding square at `smallCMInclusion D hVU`.
Their original-map inputs are the two proved properties of
`cmNormalFiniteEtale_of_dominantCriterion` with those same parameters.
Thus etaleness and finiteness are derived for the identical existing geometric
tower map; neither property is an added premise about that map.

`cmGeometricNormalFiniteEtale_of_dominantCriterion` installs these two
properties and applies `FiniteEtale.cover` to that exact map. The result lies
in `FiniteEtale.Cover Xbar_U`. Its `_left` and `_hom` theorems identify its
source with `Xbar_V` and its map with
`geometricSchemes.map (smallCMInclusion D hVU)`, both by reflexivity.
Here `Cover` is the existing category of finite-etale schemes over the base;
no additional surjectivity assertion is included in this packaging.

`cmGeometricNormalFiniteEtalePullbackIso` is an isomorphism in that cover
category from this cover to
`(FiniteEtale.pullbackFunctor π_U).obj originalCover`.
It uses the canonical `IsPullback.isoPullback`, bundled with `Over.isoMk`
and `ObjectProperty.isoMk`. Its `_hom_fst` and `_hom_snd` equations identify
the first projection of the comparison with `π_V` and the second with the
existing geometric normal tower map. Both are exactly the corresponding
pullback-isomorphism projection identities.

## Original source and scope

The contextual source is Harris and Taylor, *The Geometry and Cohomology of
Some Simple Shimura Varieties* (2001), III.1, printed pp.90–91, one-based PDF
pp.98–99, especially the moduli and finite-etale normal-cover assertions on
p.91; and III.2, printed p.96, PDF p.104, for the geometric base change used in
cohomology. It is registered as
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The book's imaginary quadratic E, CM F and totally real F+ correspond to this
module's L, F and E. The explicit cartesian level-map square and canonical
cover comparison are internal deductions from the published geometric tower
and original cover, rather than additional displayed assertions attributed to
these pages. The earlier source audit found no matching correction to this
passage in the supplied author publication-with-errata list; this is not a
claim about all possible errata.

Applicable exact representability under the source's global hypotheses,
the named dual assertions, source rigidity, a proof of the generic criterion,
full moduli comparison, canonical-model geometry and coefficient descent
remain obligations. This module supplies a conditional cover comparison on
the existing geometric schemes. It does not complete the host task.

All code and prose in this pair are by Worker 57. Only published imports are
reused. The pinned environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
