# Projective restriction of base-line trivializations

This derived construction transports the actual line-chart restriction law to
charts of a scheme over the base. Its concrete application concerns the genuine
joint frame atlases of a locally free module and a line bundle. It is an internal
consequence of the existing pullback, normalization and line-coordinate
constructions; it introduces no external mathematical assertion.

For a scheme morphism `p : X ⟶ S`, a chart `j : T ⟶ X`, an open `U` of `S`,
and a map `b : T ⟶ U.toScheme` with `j ≫ p = b ≫ U.ι`,
`openLinePullbackIso` pulls an actual trivialization of `N.restrict U.ι`
to an isomorphism from `j^*(p^*N)` to the structure module of `T`.
The construction is the canonical square pullback comparison, followed by the
pullback of `openLineIso` and the canonical structure-module comparison.
`openLinePullbackIso_hom_normalize` identifies its morphism with the existing
normalized local comparison.

For two opens `U ≤ V` and compatible chart maps `t : TU ⟶ TV`,
`openLinePullbackIso_restrict` proves the restriction formula

```text
 t^*(larger comparison) ; canonical unit comparison ; multiplication by bU^*c
   = canonical composite comparison ; smaller comparison,
```

where `c = openLineTransitionUnit eV eU h` is the actual coordinate
transition unit on the smaller base open. The hypotheses are the displayed
commutative chart equations and actual line trivializations; the restriction
compatibility of those trivializations is proved, rather than assumed.
Equivalently, the larger comparison restricts to `bU^*c` inverse times the
smaller comparison, after the canonical pullback identifications.

The concrete context has arbitrary `S : Scheme.{u}`, `M N : S.Modules`,
`n : Nat`, `hM : IsLocallyFreeOfRank M (n + 1)` and
`hN : IsLocallyFreeRankOne N`. For every arrow of their genuine joint atlas,
`dualLineProjectiveUnit_eq` identifies the existing projective coordinate
transition unit with the actual pullback of the original line-chart unit.
`TensorFrames.baseLineChartIso_restrict` proves the preceding restriction
formula for the existing `baseLineChartIso`, actual `tensorChartRestriction`
and `dualLineProjectiveUnit`. Thus the concrete result retains exactly the
local freeness assumptions of the existing tensor-line construction and adds
no compatibility hypothesis.

The proof first establishes `pullbackCongr_unit` by equality elimination.
`squarePullbackIso_unit` follows from composition coherence for canonical
structure-module comparisons; `squarePullbackIso_unit_scaled` then uses
pullback of the existing scalar automorphism and its naturality. The general
chart restriction proof supplies `openLineIso_restrict` and this scalar square
to `RefinedPullbackComparison.normalize_local_restrict_between`.
The concrete result supplies the existing cocycle chart equations and
`FrameAtlas.openCover_trans`. Its unit identification uses
`LinearSystem.scalarsFromBase_comp_toSpecΓ`.

This unit proves projective transport of the base-line scalar restriction.
Tensor scalar cancellation, compatibility of the combined local degree-one
comparisons, global gluing and the host ordinary-moduli representability
statement remain subsequent obligations.
