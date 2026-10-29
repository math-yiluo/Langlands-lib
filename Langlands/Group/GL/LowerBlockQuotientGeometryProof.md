# Geometry of the lower-block quotient chart: proof

Author: Worker 936.

This module proves the published proposition
`Langlands.RankinSelberg.LowerBlockQuotientGeometryStatement`
(module `Langlands.Group.GL.LowerBlockQuotientGeometryStatement`) as the theorem
`Langlands.RankinSelberg.lowerBlockQuotientGeometry`. The statement says that the
published chart

```text
lowerBlockQuotientChart : N_a \ GL_a × M_{d×a} × B̄_d → N_{a+d} \ GL_{a+d},
  ([g], x, h) ↦ [[[g, 0], [x, h]]],
```

for `a = n + 1` and `d = k + 1` over a p-adic field with its canonical structures,
is an open embedding, is measurable, and has `μ`-conull range for every
compatible quotient measure `μ` on `N_{a+d} \ GL_{a+d}`. The supporting results
hold for all ranks `a d` and every `T : F.TopologicalData`. They are in the
namespace `Langlands.GeneralLinear`.

## Provenance

Internal. This proves an internal Library statement, which was extracted from
`LowerBlockQuotientDisintegrationStatement` (JPSS 1983, section 9.3). It uses
the big cell `N · B̄` rather than the Schur-complement route suggested in the
statement's Markdown. The proof uses only Library results named below.

## Notation

`B̄_m = lowerTriangularSubgroup m F.Carrier`, and
`β_m = lowerTriangularQuotientMap m F.Carrier : B̄_m → N_m \ GL_m`, `b ↦ [b]`. The
block coordinates are `θ = lowerTriangularBlockMap a d F.Carrier`, with
`θ(b, x, h) = [[b, 0], [x, h]]`. Write `diag(g₀, 1) = lowerBlockPair g₀ 0 1`.

## Algebra (every commutative ring)

- `lowerBlockCellParameters g₀ (b, x, h) = ([b g₀], x g₀, h)`: the translated
  big-cell parameter map `B̄_a × M_{d×a} × B̄_d → N_a \ GL_a × M_{d×a} × B̄_d`.
- `lowerBlockQuotientChart_lowerBlockCellParameters`:
  `chart([b g₀], x g₀, h) = [θ(b, x, h) · diag(g₀, 1)]`. Proof:
  `lowerBlockPair_mul_lowerBlockPair` gives
  `[[b, 0], [x, h]] · [[g₀, 0], [0, 1]] = [[b g₀, 0], [x g₀, h]]`.
- `exists_lowerBlockCellParameters_eq`: every parameter `([g], x, h)` equals
  `lowerBlockCellParameters g (1, x g⁻¹, h)`. So the images of the translated
  parameter maps cover the parameter space.
- `mk_lowerTriangular_mem_range_lowerBlockQuotientChart`: for
  `b ∈ B̄_{a+d}`, the coset `[b]` lies in the range of the chart. Write
  `b = θ(b₁, x, h)` using `lowerTriangularBlockEquiv`; then
  `[b] = chart([b₁], x, h)`.

## Topology (p-adic field, topology `T.topology`)

- `continuous_lowerBlockCellParameters`: the translated parameter map is
  continuous. It is built from the quotient map, right multiplication in `GL_a`,
  and matrix multiplication.
- `isOpenMap_lowerBlockQuotientChart_comp_cellParameters`: by the algebraic
  identity, `chart ∘ lowerBlockCellParameters g₀` equals
  `rightTranslate _ diag(g₀, 1) ∘ β_{a+d} ∘ θ`. This is an open map: the right
  translation is a homeomorphism, `β_{a+d}` is an open embedding (published
  `isOpenEmbedding_lowerTriangularQuotientMap`), and `θ` is a homeomorphism
  (`lowerTriangularBlockHomeomorph`).
- `isOpenMap_lowerBlockQuotientChart`: for open `W`, the image `chart(W)` is
  the union over `g₀ ∈ GL_a` of the images of the open preimages
  `lowerBlockCellParameters g₀ ⁻¹' W` under these open maps, by the covering
  lemma.
- `isOpenEmbedding_lowerBlockQuotientChart`: a continuous, injective, open map
  is an open embedding. Continuity and injectivity of the chart are the
  published `continuous_lowerBlockQuotientChart` and
  `lowerBlockQuotientChart_injective`.
- `measurable_lowerBlockQuotientChart`: the chart is measurable. Here
  `N_a \ GL_a`, `N_{a+d} \ GL_{a+d}`, `F.Carrier` and `B̄_d` carry Borel
  structures, `M_{d×a}` carries Mathlib's product structure, and the parameter
  space carries the product structure. Proof: the chart is continuous. The
  product structure is Borel because `F.Carrier` is second countable
  (`T.secondCountableTopology`), hence so are `M_{d×a}` and `B̄_d`
  (`T.generalLinearSecondCountableTopology d` and the subtype embedding).
- `lowerBlockQuotientChart_range_compl_null`: take Haar measures `μG` on
  `GL_{a+d}` and `μH` on `N_{a+d}`, both regular, with `μH` right invariant, and
  a measure `μ` with `IsCompatible _ μG μH μ`. Then
  `μ (range chart)ᶜ = 0`. Proof: by the range lemma, the complement lies in
  `{q | ∀ b ∈ B̄_{a+d}, [b] ≠ q}`. That set is `μ`-null by
  `padic_lowerTriangular_leftQuotient_conull`, from
  `Langlands.Group.GL.LowerTriangularBigCellConull` (Worker 234).

## Main theorem

`lowerBlockQuotientGeometry : LowerBlockQuotientGeometryStatement`. Put
`T = F.canonicalTopologicalData`, `a = n + 1`, `d = k + 1`. The three
conjuncts are the three results above. The conull one is applied with
`μG = generalLinearHaar F.Carrier (n + 1 + k)` and
`μH = unipotentHaar F.Carrier (n + 1 + k)`. These are Haar and regular by the
published instances. Right invariance of `μH` is the statement's instance
hypothesis. The rank `n + 1 + k + 1` of the statement and the rank
`(n + 1) + (k + 1)` of the general lemmas are definitionally equal.
