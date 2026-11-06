# An identity chart of a smooth affine group over a complete field

Module `Langlands.Global.LocalModularCharacter.IdentityChart`.

Let `F` be a field and `G` a smooth affine group scheme of finite type over `Spec F`. Let `K` be
a complete nontrivially normed field that is an `F`-algebra. This module gives `G(K)` a chart at
the identity with the two derivative properties that the modular-character estimates of
`ChartEstimates` need.

This is internal infrastructure for the proof of
`Langlands.Global.PlaceGroupPoints.LocalModularCharacterAdjointDeterminantStatement`. No
literature statement is formalized here. The underlying fact is standard: a smooth group over a
complete field is an analytic group, and the derivative of conjugation by `g` at the identity
is the adjoint action `Ad(g)`. The proof combines two other helper modules of this
development: `RegularChart` (by Worker 1402) and `ChartLie`.

## Local instances

The module declares local instances only. They are not exported.

- `identityChartTopology` and `identityChartTopologicalRing` put the topology and the
  topological-ring structure of `K` on the bundled algebra `CommAlgCat.of F K`.
- `identityChartPointsTopology` and `identityChartPointsTopologicalGroup` are the Library's
  regular-function evaluation topology `G.affinePointsTopologicalSpace (CommAlgCat.of F K)` on
  `G.affinePoints (CommAlgCat.of F K)`, and the Library's topological-group instance
  `G.affinePointsIsTopologicalGroup` for it. They are stated as explicit instances because
  instance search does not find the Library instance on this type directly.
- `chartLieKernelCommGroup` and `chartLieKernelModule` (from `ChartLie`) are made local
  instances. They give the module structure on the Lie kernel in which `adjoint G K g` is a
  linear map.

## Main theorem

`exists_identityChart (hG : Smooth G.X.hom)`, with `[IsAffine G.X.left]`,
`[LocallyOfFiniteType G.X.hom]`, `[IsAffineHom G.X.hom]` and a complete nontrivially normed
field `K` in the same universe as `F`. It states that there are `d : ℕ` and an open partial
homeomorphism `φ : G(K) → K^d` such that:

1. `1 ∈ φ.source` and `φ 1 = 0`;
2. the chart expression `(p, q) ↦ φ(φ⁻¹ p · φ⁻¹ q)` of the group law has a strict derivative
   `L` at `(0, 0)` with `L (0, w) = w` for all `w`;
3. for every `g ∈ G(K)`, the chart expression `z ↦ φ(g · φ⁻¹ z · g⁻¹)` of conjugation by `g`
   has a strict derivative at `0` given by a continuous linear automorphism `A` of `K^d` with
   `det A = det (adjoint G K g)`.

Here `G(K)` is `G.affinePoints (CommAlgCat.of F K)` with the evaluation topology above.

## Proof

Let `e := G.affinePointsAlgebraHomeomorph (CommAlgCat.of F K)` (Library). It identifies `G(K)`
with the space of `F`-algebra points `AlgPoint F (AffineCoordinateRing F G.X) K`, and
`affinePointsAlgebraHomeomorph_apply` says that it matches regular-function evaluations. Apply
`exists_regularChart` (module `RegularChart`) to the point `e 1`. This gives a chart `φ₀` of
the algebra-point space, coordinates `c`, and a strictly differentiable `R` with derivative `R'`,
with the properties listed in `RegularChart.md`. The chart is `φ := e ≫ φ₀`
(`Homeomorph.transOpenPartialHomeomorph`). The four hypotheses of `chart_derivatives`
(module `ChartLie`) are the corresponding properties of `φ₀`, rewritten with
`affinePointsAlgebraHomeomorph_apply` and `e (φ.symm s) = φ₀.symm s`. `chart_derivatives` then
gives conclusions 2 and 3 directly.
