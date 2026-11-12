# Proof: adelic fibre products over a nonseparated base fail for the doubled-origin line

Authors: Worker 3519 and Worker 129. Worker 3519 supplied the complete proof draft;
Worker 129 checked its source correspondence and prepared it for submission.

This module proves `Langlands.Global.AdelicSpreadNonseparatedPullbackStatement`. The entry
theorem is `Langlands.Global.adelicSpreadNonseparatedPullback`. The statement is the
counterexample to an unrestricted reading of a sentence on printed p.9 of Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011; registered as
`conrad-2011-weil-grothendieck-adelic-points`, PDF SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`). That sentence says the adelic topology is
"compatible with fiber products for general `X`". The statement's Markdown explains the
source and the example.

## Route

The proof does not compute the topology of the pullback directly. It shows instead that a
homeomorphic comparison would make `Aˣ → A` a topological embedding, which
`adelicPunctureEmbedding` refutes. The limit hypothesis on the cone is not used: the
argument works for every cone over the two charts.

### Reduction from generic fibres to models

`isHomeomorph_of_imagePullbackPointComparison` is the converse of the reduction used in
`AdelicSpreadModelPullbackProof`. Take homeomorphisms `e W` from the points of models `W` to
the points of their images `G.obj W`, natural in `W`. If the comparison for the image cone
`c.map G` is a homeomorphism, so is the comparison for `c`, since it equals
`E⁻¹ ∘ H ∘ e c.pt`. Here `H` is the image comparison and `E` is the product homeomorphism on
compatible pairs. The final theorem applies this with `G` the base change from the
`S`-integers to the global field, the fixed-model topologies on model points, and the spread
homeomorphisms `curvePlaceSpreadAdelePointHomeomorph`, `numberFieldSpreadAdelePointHomeomorph`.
Naturality is `curvePlaceGenericFiberAdelePointEquiv_natural` and
`numberFieldGenericFiberAdelePointEquiv_natural`, exactly as in `adelicSpreadModelPullback`.
This yields a homeomorphic fixed-model comparison over the `S`-integers.

### The core argument

`doubledOrigin_pullbackComparison_not_isHomeomorph` works over any commutative ring `R` and any
topological `R`-algebra `A` for which `Units.val : Aˣ → A` is not an embedding. It assumes a
family `τ` of topologies on points of schemes over `Spec R` such that:

- postcomposition with every morphism is continuous;
- the coordinate maps `linePoint R A : A → L(A)`, `a ↦ ringTestMap R (aeval a)`, and
  `lineCoord R A : L(A) → A`, `q ↦ (affineRingPointEquiv R R[X] A q) X`, are continuous for
  `τ` on the affine line `L = ringTest R R[X]`.

`linePoint` abbreviates the existing affine-line evaluation construction
`HenselianIntegralPointsNotClosed.linePoint`, with the coefficient ring `A`
explicit in this module's interface.

Let `c` be a cone over the charts `doubledOriginChart R true` and `doubledOriginChart R false`,
and suppose the comparison `Φ` is a homeomorphism `H`. Then:

1. **A map to the inverse coordinate.** `c.condition` gives equal composites of the two legs
   into the glued scheme. `CommonOpenGluing.exists_of_comp_eq` factors the first leg as
   `w₀ ≫ g₁` through the common open `Spec B₂`, where `g₁ = Spec α` and `α t = s - 1`. In `B₂`
   the element `α X = s - 1` is a unit; let `v` be its inverse. The morphism
   `m = w₀ ≫ Spec (aeval v) : c.pt ⟶ L` lies over `Spec R`, by `α_comp_algebraMap` and
   `AlgHom.comp_algebraMap`.
2. **Compatible pairs.** For `u : Aˣ`, the points `t = u` of the first chart and `s = u + 1`
   of the second have the same image in the glued scheme
   (`DoubledPointLine.ringTestMap_aeval_chart_eq` with `p = 1`). This gives a map `pair` from
   `Aˣ` to the compatible pairs. It is continuous for the topology on `Aˣ` induced by
   `Units.val`, by continuity of `linePoint`.
3. **The composite is inversion.** Put `inv' u = lineCoord (H⁻¹ (pair u) ≫ m)`. For
   `w = H⁻¹ (pair u)` we have `w ≫ c.fst = linePoint u`. Let `ω` be the ring map with
   `Spec ω = w.left ≫ w₀`. Comparing spectra gives `α ≫ ω = aeval u`, so `ω (s - 1) = u`. The
   point `w ≫ m` is `ringTestMap R ψ` for its coordinate algebra map `ψ`, and comparing spectra
   gives `ψ = ω ∘ aeval v`. Hence `inv' u = ω v`, and `ω v * u = ω (v (s - 1)) = 1`, so
   `inv' u = u⁻¹`.
4. **Conclusion.** `inv'` is continuous for the induced topology: it composes `pair`, `H⁻¹`,
   postcomposition with `m` and `lineCoord`. By `Units.topology_eq_inf`, the units topology is
   the infimum of the topologies induced by `u ↦ u` and `u ↦ u⁻¹`. Continuity of
   `u ↦ u⁻¹` for the first therefore makes `Units.val` inducing, hence an embedding.

### Instantiation

Each arithmetic case uses the following inputs:

- the fixed-model topologies `curvePlaceFixedModelAdelePointTopology` and
  `numberFieldFixedModelAdelePointTopology`;
- functoriality from `adelicFixedModelFunctoriality`;
- continuity of the line coordinates: rewrite with
  `curvePlaceFixedModelAdelePointTopology_eq_affine` or
  `numberFieldFixedModelAdelePointTopology_eq_affine` (the affine line is affine, of finite
  type and of finite presentation; the last instance is
  `ringTest_polynomial_locallyOfFinitePresentation`), then use
  `continuous_linePoint` and `continuous_lineCoord`. These follow from
  `spectrumAlgebraPointHomeomorph`, `AlgPoint.continuous_iff` and `Polynomial.continuous_aeval`;
- the non-embedding clause of `adelicPunctureEmbedding`, for the curve-place and the
  number-field adeles.

The finite-type clauses of the statement are `DoubledPointLine.locallyOfFiniteType_hom` and
`DoubledPointLine.quasiCompact_hom` with `p = 1`.

The module uses `set_option maxHeartbeats 800000` and the two `backward` options of
`AdelicSpreadModelPullbackProof`, which the reduction step needs to elaborate. It depends only
on `propext`, `Classical.choice` and `Quot.sound`.
