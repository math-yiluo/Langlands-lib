# Original CM unramifiedness and finite-etale self-pullback

Author: Worker 57.

Under the existing exact representation witnesses, both named relative-dual
assertions and explicit geometric coarse rigidity, this derived construction
proves formal unramifiedness of the original CM normal forgetting map. It
constructs the map's actual self-pullback as an object of the existing
finite-etale cover category over the fine scheme. Its underlying scheme and
morphism are reflexively the original kernel pair and its first projection.
It also proves that etaleness of the original projection is equivalent to
flatness of that same projection. Flatness itself remains open.

## Parameters and original geometry

All declarations lie in
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`. The universe-zero arithmetic
inputs are a totally real number field `E`, its quadratic CM number-field
extension `F`, the displayed algebra and scalar-tower structures for `A`,
`D : CentralSimpleUnitaryData E F A n`, an imaginary quadratic CM number
field `L` with its algebra map to `F`, and `τ₀ : L →+* ℂ`. The charts `C`
use exactly `harrisCMSection E (algebraMap L F) τ₀`.

The named infrastructure inputs remain tensor-pullback comparison preservation,
composition, unit coherence, associativity, left-unitor comparison and symmetry;
Picard-zero pullback, the Mumford-bundle assertion and universal base change;
dual-abelian base-change naturality; polarization base-change stability;
relative finite Weil transition; the rational/profinite-integer/adele
comparison; and torsion finite etaleness. The imported moduli functor retains
its conjugated Harris–Taylor reflex normalization, positive auxiliary
involution, polarizations, Weil pairings and rational-isogeny equivalence with
an actual rational inverse. Determinant and dimension conditions remain on a
common representative. No invariance of dimension under arbitrary rational
isogenies is added.

`R` supplies the existing `CMLevelRepresentation` witnesses at every
`SmallCMLevel D`, with their actual representing isomorphisms for the fixed
componentwise CM class presheaf, actual schemes, smoothness and projective-space
witnesses. Fix `U V : SmallCMLevel D`, the original inclusion
`hVU : V.obj.subgroup ≤ U.obj.subgroup`, and normality of
`V.obj.subgroup.subgroupOf U.obj.subgroup`.

Write `X_V`, `X_U`, `p` and `Q` for the original represented fine and coarse
schemes, `representedCMNormalProjection R U V hVU`, and
`SmallCMResidualGroup D U V`. The copies scheme is the original coproduct
of `X_V` over `Q`, and `K` is the original pullback
`X_V ×[X_U] X_V`. Its original comparison `κ` is exactly
`representedCMNormalKernelComparison R U V hVU`. On summand `g`, it is the
existing graph `(identity, ρ(g))` of the original residual action with its
inverse-right frame convention.

The explicit additional hypotheses are
`RelativeDualSchemeExistenceStatement.{0}`,
`RelativeDualSchemeGeometryStatement.{0}` and
`CMGeometricCoarseRigidity ... U.obj`. The dual hypotheses supply universal
Picard-zero duals over quasi-separated bases and their smoothness, properness
and geometric connectedness. Geometric coarse rigidity is the actual
original no-automorphisms condition on every admitted algebraically closed
universe-zero field spectrum with its original representative tests; it is
not inferred from source smallness. These remain the same substantive premises
as in the imported full scheme inverse of `κ`.

## Graphs, diagonal and formal unramifiedness

`representedCMNormalGraph_isOpenImmersion_of_dualGeometry` obtains
`IsIso κ` from the already constructed original kernel scheme isomorphism.
The exact equation
`representedCMNormalKernelComparison_ι` writes each original graph as its
original coproduct summand inclusion followed by `κ`. The summand inclusion
is an open immersion and `κ` is an isomorphism, so the original graph is
an open immersion.

`representedCMNormalProjection_diagonal_isOpenImmersion_of_dualGeometry`
takes `g = 1`. The existing `representedCMNormalGraph_one` identifies that
identical graph with `pullback.diagonal p`. Transporting the proved
open-immersion property gives the original diagonal open immersion.
`representedCMNormalProjection_formallyUnramified_of_dualGeometry` applies
Mathlib's implication from an open-immersion diagonal to
`FormallyUnramified p`. These are assertions about the original scheme maps,
not just their geometric points. No original-projection etaleness is used.

## Actual finite-etale self-pullback

`representedCMNormalSelfPullback_etale_of_dualGeometry` uses the exact
original comparison equation

```text
κ ≫ pullback.fst p p = Sigma.desc (fun _ : Q => 𝟙 X_V).
```

The right side is etale by the Zariski-local-at-source `sigmaDesc` criterion
applied to identity morphisms. Since the previously proved `κ` is an
isomorphism, cancellation of an isomorphism for the etale morphism property
gives `Etale (pullback.fst p p)`.

`representedCMNormalSelfPullbackFiniteEtale` separately obtains
`IsFinite p` from
`representedCMNormalProjection_isFinite_of_dualGeometry`. That earlier
result proves finite point fibers from the original residual translates and
uses original properness and local quasi-finiteness; it has no original
etaleness or rigidity premise. Finiteness is stable under base change, so
the actual first projection of the actual self-pullback is finite as well.

The definition applies the existing `cover` constructor to precisely
`pullback.fst p p`, using these proved finite and etale properties. Its target
is `Langlands.AlgebraicGeometry.FiniteEtale.Cover X_V`.
`representedCMNormalSelfPullbackFiniteEtale_left` and
`representedCMNormalSelfPullbackFiniteEtale_hom` are reflexive equalities
identifying its underlying scheme with the original `K` and its morphism with
the original `pullback.fst p p`. This is the self-base-change of the original
projection along itself. It does not assert etaleness of `p` before base
change.

## Exact remaining flatness condition and chosen specialization

`representedCMNormalProjection_etale_iff_flat_of_dualGeometry` first installs
the proved `FormallyUnramified p`. The original coarse scheme is locally
Noetherian by `(R U).base.property.locallyNoetherian`, and original properness
gives `LocallyOfFiniteType p`. Mathlib's
`LocallyOfFinitePresentation.iff_locallyOfFiniteType` over a locally
Noetherian target supplies local finite presentation. An etale morphism is
flat; conversely Mathlib's
`AlgebraicGeometry.Etale.of_formallyUnramified_of_flat` applies to these
proved properties and a supplied `Flat p`. Thus the result is exactly
`Etale p ↔ Flat p`. No flatness premise is needed by the construction of the
self-pullback cover, and flatness of the original projection is not proved.

For the exact proposition `q : CMRepresentabilityStatement ...`, all chosen
declarations substitute precisely `chosenCMLevelRepresentation ... q` for
`R`, the same family defining `cmSchemeTower ... q`.
`cmNormalProjection_formallyUnramified_of_dualGeometry` uses the direct
original chosen tower map at `smallCMInclusion D hVU`.
The entry `cmNormalSelfPullbackFiniteEtale` is the finite-etale self-pullback
for this identical family. Its `_left` and `_hom` equations are reflexive;
the morphism is the actual self-pullback first projection of that direct
chosen tower map.
`cmNormalProjection_etale_iff_flat_of_dualGeometry` states the same
equivalence for the direct chosen forgetting map.

## Provenance and retained source obligations

This is an internal deduction from the constructed original kernel scheme
inverse, its original graph equations, the proved original finiteness and
the pinned Mathlib morphism-property facts described above.

Harris and Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.1, printed pp.90–91, one-based PDF pp.98–99, is
registered as
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The passage specifies local torsion-free smallness, the product over
connected components, polarized CM frame-orbit moduli, isogeny equivalence
with rational polarization multiplier and right frame composition. It asserts
smooth projective representability, finite-etale forgetting and the normal
`U/V` Galois cover. The imported objects retain those conventions. The
conditional formal unramifiedness and self-pullback construction here are
not presented as proofs of all those stronger source assertions. The
supplied publication/errata list was previously read in full and lists no
correction to this passage.

Applicable representability, derivation of the exact geometric rigidity
hypothesis from source smallness, comparison with the complete source moduli
problem, original projection flatness and etaleness, canonical-model geometry
and coefficient descent remain separate obligations. Arbitrary scheme
structure and nilpotents are preserved. This construction supplies no
section of the original forgetting projection and does not complete the
source cover theorem or the host task.
