# Geometric input for the one-dimensional classification

Worker 716. This module derives the hypotheses of the algebraic core
`exists_primitive_bijective` (module `Core`) from the geometric assumptions of
`Langlands.GroupScheme.PerfectFieldOneDimensionalUnipotentStatement`. The
assumptions are smoothness of relative dimension one, connectedness and
unipotence. It is stated for a corepresented group
`Corepresented.groupScheme F e` with coordinate algebra `B`, whose underlying
scheme is `Spec B`. No registered source was used; the arguments are the
implemented ones and rely on published Library results.

## Results

- `finiteType_of_smooth`: if the structure map is smooth, `B` is a finitely
  generated `k`-algebra. `Corepresented.smooth_groupScheme_iff` gives
  `Algebra.Smooth k B`, which implies finite type.
- `ringKrullDim_le_one`: under `SmoothOfRelativeDimension 1`,
  `ringKrullDim B ≤ 1`. The Library theorem
  `Langlands.AlgebraicGeometry.fieldSmoothTopologicalKrullDim` bounds the
  topological Krull dimension of a quasi-compact scheme smooth of relative
  dimension `g` over a field by `g`. Mathlib's
  `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim` converts this to the
  Krull dimension of `B`.
- `exists_not_mem_span_one`: under `SmoothOfRelativeDimension 1`, with `B` a
  domain, some element of `B` is not a constant. Otherwise
  `algebraMap k B` would be bijective, and the structure map an isomorphism
  onto the one-point space `Spec k`. The unique point is closed, and the
  Library theorem `fieldSmoothClosedPointStalkDimension` would give its stalk
  Krull dimension as `1`. The structure map is an isomorphism, so it is also
  smooth of relative dimension `0`, and the same theorem gives `0`. This is a
  contradiction.
- `isDomain_tensor`: if the structure map is smooth and the space is
  connected, `B ⊗[k] B` is a domain. The Library theorem
  `smoothConnectedAffineGeometry` makes the structure map geometrically
  integral. Base change to `K = FractionRing B` gives an integral scheme
  `Spec (B ⊗ K)`, via `isPullback_SpecMap_of_isPushout` and
  `CommRingCat.isPushout_tensorProduct`. So `B ⊗ K` is a domain
  (`affine_isIntegral_iff`). The map `B ⊗ B → B ⊗ K` is injective, because
  `B` is flat over the field `k` (`Module.Flat.lTensor_preserves_injective_linearMap`).
  So `B ⊗ B` is a domain.
- `not_isUnit_aeval`: let the structure map be smooth, `B` a domain, `z` a
  nonzero primitive element and `g` a nonconstant polynomial. Then `g(z)` is
  not a unit. The Library theorem
  `isFppfQuotient_quotientMap_of_isPrimitiveElem` makes the map to the
  additive group defined by `z` an fppf quotient, in particular surjective on
  spectra. By `VectorGroup.quotientMap_left`, the underlying scheme map is the
  spectrum of `MvPolynomial.aeval (fun _ => z)`. The nonconstant polynomial
  `G = g(X₀)` in `MvPolynomial (Fin 1) k` is not a unit, so it lies in a
  maximal ideal `m`. A prime of `B` lying over `m` contains `g(z)`, so `g(z)`
  is not a unit.

## Main result

`exists_primitive_bijective_of_smooth` requires `k` perfect, the structure
map smooth of relative dimension one, the space connected and the group
unipotent. It gives a primitive `y ∈ B` such that `aeval y : k[X] → B` is
bijective.

It feeds `exists_primitive_bijective` with:

- `IsDomain B` (Library `isDomain_of_smooth_connected`), together with
  `isDomain_tensor` and `finiteType_of_smooth`;
- `OneMemStable` (Library `oneMemStable_of_isUnipotent`);
- `exists_not_mem_span_one`;
- the finiteness of `B/(z)` (`finite_quotient_span_singleton` with
  `ringKrullDim_le_one`);
- the dependence of two elements (`exists_ev2_eq_zero` with `trdeg_le_one`),
  all from `Dimension`;
- `not_isUnit_aeval`.
