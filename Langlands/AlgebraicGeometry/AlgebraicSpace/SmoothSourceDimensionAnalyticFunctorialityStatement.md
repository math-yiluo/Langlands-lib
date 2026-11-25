# Analytic functoriality across actual smooth dimension pieces

This derived statement supports the functorial analytic-manifold assertion in
Brian Conrad, *Weil and Grothendieck approaches to adelic points*, December 31,
2011, printed p.15, Proposition 5.4, and the final paragraph of its proof on
printed p.16. The registered original is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The paper permits dimensions to vary between smooth components. This module
states the bridge from an admissible pure-dimensional family to the
actual varying-dimensional atlases. It contains no proof; the statement is
proved as `smoothSourceDimensionAnalyticFunctoriality` in
`SmoothSourceDimensionAnalyticFunctorialityProof`.

`SmoothSourceDimensionAnalyticFunctorialityStatement` is a proposition
definition in `Langlands.AlgebraicGeometry.AlgebraicSpace`.
Let `K` be a nontrivially normed henselian valued field and let
`σ : AnalyticPointStructure K` satisfy `σ.IsAdmissible`. This premise is the
conjunction of analytic pure-dimensional manifold structures, analytic
functoriality between them, étale local analytic isomorphisms, and agreement
with affine-space coordinates. Let `X` and `Y` be actual smooth algebraic
spaces over `Spec K`, each quasi-separated and locally separated. These four
separation hypotheses are supplied individually. Smoothness supplies local
finite type. The statement requires no quasi-compactness, uniform dimension,
finite range of dimensions, nonempty point space, or completeness.

For every actual algebraic-space morphism `f : X ⟶ Y`, the conclusion is
analyticity of the actual point map `RingPoints.map (A := K) f` between
`σ.dimensionAtlas hK hX hXqs hXls` and
`σ.dimensionAtlas hK hY hYqs hYls`. Both carriers are the original rational
point sets; both topologies are the independently defined étale-chart
topologies. Each atlas uses the genuine open dimension pieces and all their
supplied pure-dimensional charts, lifted through the actual piece inclusions.

More explicitly, `DimensionPointAtlas.AnalyticMap` includes continuity of the
point map for the original topologies. For every source dimension `n`, target
dimension `m`, source atlas chart `e` and target atlas chart `e'`, it requires
`ContDiffOn K ω (e' ∘ RingPoints.map f ∘ e.symm)` on

```text
e.target ∩ e.symm ⁻¹' (Set.univ ∩ (RingPoints.map f) ⁻¹' e'.source).
```

The target-chart preimage is retained in full. A general morphism can send
different open parts of a single source dimension piece into different target
dimension pieces, and `n` and `m` need not coincide. The conclusion quantifies
every such chart intersection, including empty ones. It does not assert
intrinsic dimension preservation for general morphisms.

The mathematical route of a proof restricts a source piece to its
intersection with the inverse image of a target piece. This is a genuine
open subspace, still smooth of the source piece's pure dimension. The
restriction inclusion is étale, and the restricted map to the target piece
is a morphism between pure-dimensional spaces, of possibly different
dimensions. The supplied family's étale local analytic isomorphisms and
functoriality then give the coordinate assertion locally on every displayed
intersection. This restriction is necessary; no map from an entire source
dimension piece to a single target dimension piece is assumed.

Conrad states the full analytic structure over complete fields. Here the
admissible family is retained as an explicit premise, so this assembly
comparison does not need completeness. A complete-field application must
supply an admissible family separately. This module neither constructs that
family nor proves this bridge, intrinsic dimension preservation and analytic
inverse branches for étale maps, scheme agreement, or uniqueness of the full
varying-dimensional structure. These are separate results: over a complete
field the canonical family is admissible by `canonicalAnalyticPointStructure_isAdmissible` in
`AnalyticAffineNormalization`, the bridge is proved in
`SmoothSourceDimensionAnalyticFunctorialityProof`, and the others in
`SmoothSourceDimensionEtaleAnalyticIsoProof`,
`SmoothSourceDimensionAffineAgreement` and
`SmoothSourceDimensionAnalyticUniquenessProof`.
