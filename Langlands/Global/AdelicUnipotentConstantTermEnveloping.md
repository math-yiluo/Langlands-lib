# The enveloping action on unipotent constant terms

The section `Unipotent` works with a closed immersion `j : U → G` of affine group schemes over
`F`, with `G` locally of finite type and smooth of relative dimension `d` (`hG`). Write
`CT = subgroupConstantTerm F j`, the integral over `U(F)\U(𝔸)` for the normalized quotient
measure, with the integrand evaluated at chosen representatives.

- `integrable_subgroupConstantTermIntegrand_of_unipotentInvariant`: if `U` is smooth, connected and unipotent and `f`
  is continuous and left invariant under the image of `U(F)`, then for every `g` the integrand
  `z ↦ f(z g)` is integrable. It descends to a continuous function on the quotient
  `U(F)\U(𝔸)`, which is compact (`compactSpace_rationalQuotient_range_unipotent`) and carries a
  probability measure.
- `subgroupConstantTerm_add_of_unipotentInvariant`: hence `CT (f₁ + f₂) = CT f₁ + CT f₂` for
  two such functions. `subgroupConstantTerm_smul` and `subgroupConstantTerm_zero` record
  `CT (c • f) = c • CT f` and `CT 0 = 0`, which hold for all functions.
- `IsSmoothUnipotentInvariant j hG L f` bundles the hypotheses on `f` of
  `AdelicUnipotentConstantTermDifferentiationStatement`: `f` is continuous, each infinite slice
  `y ↦ f(pair y b)` is smooth for the manifold structure `smoothChartedSpace F G hG`, `f` is left
  invariant under the image of `U(F)`, and right invariant under the finite-adelic subgroup `L`.
  The class is closed under sums (`IsSmoothUnipotentInvariant.add`) and complex multiples
  (`IsSmoothUnipotentInvariant.smul`), and its slices lie in `InfinitePlotSmoothFunctions F G`
  (`IsSmoothUnipotentInvariant.slice_mem`, by `isPlotSmooth_iff_contMDiff`).

`isCenterFiniteFunction_subgroupConstantTerm` proves: if `U` is smooth, connected and unipotent,
`L` is open, `f` lies in the class and `IsCenterFiniteFunction F G hG hcalc f` holds with an
ideal `J` of finite codimension in the center of the complex enveloping algebra of `G(F_∞)`, then
`IsCenterFiniteFunction F G hG hcalc (CT f)` holds with the same ideal `J`.

The proof uses a private predicate on elements `u` of the enveloping algebra: for every `f` in the
class there is `g` in the class such that, at every finite point `b`, `u` maps the slice of `f`
at `b` to the slice of `g` at `b` and maps the slice of `CT f` at `b` to the slice of `CT g` at
`b` (for the action `plotSmoothEnvelopingAction`). Every `u` is the image of an element `t` of
the tensor algebra (`RingCon.mkₐ_surjective`), and the predicate is proved by induction on `t`:

- a complex scalar `c` acts by multiplication; take `g = c • f`;
- a generator `c ⊗ X`, with `X` a real tangent vector at the identity, acts by `c` times the
  directional derivative (`plotSmoothEnvelopingAction_generator`,
  `complexPlotSmoothLieAction_tmul`, `plotSmoothDifferential`). Take
  `g = c • adelicDirectionalValue hG X f`, the multiple of the right-orbit derivative.
  `adelicUnipotentConstantTermDifferentiation` shows that this derivative lies in the class
  again and that the derivative in direction `X` of the slice of `CT f` is the slice of the
  constant term of the derivative; `adelicDirectionalValue_pair` identifies the right-orbit
  derivative on a slice with the directional derivative of the slice;
- for sums of generators and of tensor-algebra elements take the sum of the two functions,
  using the additivity of `CT` on the class;
- for a product `x * y`, apply the predicate for `y` to `f` and then the predicate for `x` to
  the resulting function.

For `z ∈ J`, `z` annihilates every slice of `f`. The function `g` attached to `z` therefore has
zero slices, so `g = 0`, because every adelic point is the pair of its infinite and finite
projections (`pair_projections`). Hence `z` maps every slice of `CT f` to the slice of
`CT 0 = 0`.
