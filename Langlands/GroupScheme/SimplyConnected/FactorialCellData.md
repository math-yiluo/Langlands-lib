# Coordinate split data and big-cell charts over a field

This internal helper module, used in the proof of
`SplitSimplyConnectedFactorialStatement`, packages the coordinate split
structure of a reductive group `G` over a field `k`. It defines the big-cell
charts and the subgroups spanned by the root groups of closed sets of roots.

## The data

`CellData k G` (for `G` over `Spec k` with affine structure map) consists of:

- a finite index type `I` and a closed coordinate split torus
  `i : splitTorus (Spec k) I ⟶ G` that is a fibrewise maximal torus;
- the reductivity of `G`;
- a coordinate root datum `P : RootDatum J (I → ℤ) (I → ℤ)` with
  `IsFibrewiseRootDatumOf I G i P` (so `J` is finite and `P` is reduced, the
  instances `finiteJ` and `isReduced`);
- a base `b` of `P`;
- root parametrizations `u α : Ga k ⟶ G` (`IsRootParametrization`);
- for every simple root `a`, the Weyl point
  `weylPoint (u a) (u (-a)) = u_{-a}(-1) u_a(1) u_{-a}(-1)` (the Library's
  `LocalSplitCell.weylPoint`; `-a` is written `P.reflectionPerm a a`) normalizes
  the torus and acts as the reflection `s_a` (`IsWeylPoint`).

These are the hypotheses of the Library's `affineSplitRootSubgroupSpanning` and
of the rank-one laws of `LocalSplitCell`. The proof module builds such data in
`nonempty_cellData`.

## Charts

For enumerations `neg : Fin m ≃ {negative roots}` and
`pos : Fin n ≃ {positive roots}`:

- `isOpenImmersion_cellMap`: the big-cell map
  `(v, t, w) ↦ ∏ u_{neg r}(v_r) · i(t) · ∏ u_{pos r}(w_r)` is an open immersion
  (clause 1 of `affineSplitRootSubgroupSpanning`).
- `chart neg pos : cellSpec k I m n ⟶ G.X` is `cellCoordHom` (module
  `FactorialCellRing`) followed by the big-cell map. It is an open immersion
  (`isOpenImmersion_chart`). By `comp_chart`, a point `z` of `cellSpec` maps to
  the cell point with coordinates `pointRing z (v_r)`, the torus point
  `z ≫ specTorus` and `pointRing z (w_r)`.

## Root subgroups of closed sets of roots

- `IsClosedRootSet Ψ`: `Ψ` is closed under sums of roots and contains no pair of
  opposite roots.
- `exists_rootSpan` (clause 3 of `affineSplitRootSubgroupSpanning`): for a
  closed set `Ψ` there are a group scheme `H` and a map `j : H ⟶ G` whose image is
  stable under conjugation by torus points. For every enumeration
  `e : Fin n ≃ Ψ`, `j` is identified with the ordered product of the root groups
  along `e` on the vector group `𝔾ₐⁿ`.
- `rootSpanGroup`, `rootSpanHom` and `rootSpanHom_spec` choose such `H` and `j`;
  `rootSpan hΨ` is the range of `j` as a subgroup functor of `G`.
- `orderedProduct_mem_rootSpan` and `exists_eq_orderedProduct`: the points of
  `rootSpan hΨ` are exactly the ordered products `∏ u_{e r}(c_r)`, for any fixed
  enumeration `e`.
- `rootPoint_mem_rootSpan`: `u_α(c) ∈ rootSpan hΨ` for `α ∈ Ψ`.
- `torus_conj_mem_rootSpan`: `rootSpan hΨ` is stable under conjugation by points
  of the torus.

Provenance: internal packaging of the Library's coordinate split results
(`affineSplitRootSubgroupSpanning`, `LocalSplitCell`).
