# Analytic functoriality for all smooth dimension pieces

The theorem
`Langlands.AlgebraicGeometry.AlgebraicSpace.smoothSourceDimensionAnalyticFunctoriality`
proves the unchanged published proposition
`Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothSourceDimensionAnalyticFunctorialityStatement.{u}`
for every universe `u`.

Let `K` be a nontrivially normed henselian valued field and let
`σ : AnalyticPointStructure K` satisfy `σ.IsAdmissible`. For any morphism
`f : X ⟶ Y` between actual smooth, quasi-separated, locally separated
algebraic spaces over `Spec K`, the actual point map `RingPoints.map f` is an
`AnalyticMap` between the two atlases `σ.dimensionAtlas`. This includes
continuity for the original étale-chart topologies and the analytic coordinate
condition for every source chart and target chart, in arbitrary dimensions.
The carriers remain the original rational point sets.

The provenance is Brian Conrad, *Weil and Grothendieck approaches to adelic
points*, December 31, 2011, printed p.15, Proposition 5.4, and the final proof
paragraph on printed p.16. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
This dimension assembly lemma is derived content supporting that proposition;
it is not a separately numbered assertion in the source. The paper's full
analytic structure is stated over complete fields. Here an admissible family
is an explicit premise; this proof does not construct it.

## Local analytic lift

The private helper `exists_analytic_lift` works with pure-dimensional smooth
spaces `P` and `Q` of dimensions `n` and `m`, an open immersion `j : Q ⟶ Y`,
and a morphism `F : P ⟶ Y`. Given points `x` and `y` with `F(x) = j(y)`,
it constructs a function `H : P(K) → Q(K)` that is analytic at `x`, takes
`x` to `y`, and satisfies `j(H(z)) = F(z)` throughout a neighborhood of `x`.
Only this local behavior of the globally defined function is used.

Choose a pure-dimensional smooth affine scheme chart `c` over `P` and a
rational point above `x`, using `smoothPureDimensionalAffineChart`. Pull `j`
back along the scheme-valued map `c.hom ≫ F`, using its actual representability
data. The resulting scheme `V` is open in the chart scheme. Composition of
this open immersion with the chart's smooth structural morphism makes `V`
smooth of relative dimension `n`. Its associated algebraic space is therefore
smooth pure-dimensional of dimension `n`.

The pullback has maps `p : V ⟶ P` and `g : V ⟶ Q`, with `p` étale.
The theorem `exists_pullback_point` gives a rational point `v` above both the
chosen chart point and `y`. Thus `p(v) = x` and `g(v) = y`. Admissibility
supplies a local analytic inverse to `p` at `v` and analyticity of `g`
between dimensions `n` and `m`. Define `H` as `g` composed with this local
inverse. The local inverse identities and the pullback square establish its
value at `x` and the required neighborhood equality.

## All chart intersections

Continuity follows from the published `continuous_ringPointsMap`, using the
henselian field hypothesis and the separation and finite-type properties
of the target.

Fix arbitrary dimensions `n` and `m` and arbitrary assembled charts. Unpack
them as lifts of charts `c` on the source piece `P = X_n` and `d` on the
target piece `Q = Y_m`. At any point `z` of the full coordinate domain

```text
e.target ∩ e.symm ⁻¹' (Set.univ ∩ (RingPoints.map f) ⁻¹' e'.source),
```

membership supplies a point `y` of `d.source` with
`f(j_P(c.symm(z))) = j_Q(y)`. Apply the local helper to `F = j_P ≫ f`
and the genuine open immersion `j_Q`. It gives an analytic local lift `H`
at `c.symm(z)` with value `y`.

The manifold atlas properties of the admissible family make `c.symm`
analytic at `z` and `d` analytic at `y`. Their composition `d ∘ H ∘ c.symm`
is analytic at `z`; `contMDiffAt_iff_contDiffAt` converts this to the required
coordinate-space assertion. Continuity of `c.symm` pulls the helper's
neighborhood equality back to a neighborhood of `z`. Evaluation of a lifted
chart on the image of its open embedding agrees with the original chart.
Consequently the actual coordinate map `e' ∘ RingPoints.map f ∘ e.symm`
agrees there with `d ∘ H ∘ c.symm`. Eventual equality transfers analyticity,
which restricts to the displayed chart domain.

The dimensions may differ, and the argument does not assume that a whole
source piece maps into one target piece. Quantification includes dimension
zero, empty intersections, and all natural-number dimension pieces. No
quasi-compactness, finite dimension range, or completeness hypothesis is added.
