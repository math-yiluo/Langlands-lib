# Extending isometries from a nondegenerate block of rows

This module generalizes the hyperbolic-plane extension
`HyperbolicScheme.isometryHom` (module
`Langlands.GroupScheme.Quaternionic.HyperbolicGroupSchemeExtension`) from a
hyperbolic plane to an arbitrary block of rows whose polar Gram matrix is
invertible. All declarations are in the namespace
`Langlands.GroupScheme.Quaternionic.SubspaceScheme`.

The setting is the following. `K` is a field, `D` is a division `K`-algebra,
and `σ : FirstKindInvolution K D`. The index types `n` and `k` are finite types
in `Type` with decidable equality. `q : σ.QuadraticForms n` is a quaternionic
quadratic form on `D^n`, and `E : Matrix k n D` is a matrix whose rows span a
subspace `W`. Write

- `B = σ.polar q` for the polar Gram matrix of `q`,
- `E*` for `σ.rectangularAdjoint E`,
- `G = E B E*` for the polar Gram matrix of the rows of `E`.

The only hypothesis is `hE : IsUnit (E * σ.polar q * σ.rectangularAdjoint E)`,
that is, `G` is invertible: the polar form is nondegenerate on `W`. The rows of
`E` need not be the hyperbolic pair or any particular basis. No centrality,
local-field, Witt-index, dimension or characteristic assumption is made. The
group-scheme part also assumes `[FiniteDimensional K D]`, which the
matrix-unit group schemes require.

## Polar coordinates (section `Algebra`)

- `sesqForm_vecMul_vecMul` changes both arguments of a sesquilinear form by
  square matrices: `h_H(x A, y C) = h_{A H C*}(x, y)`.
- `retractionMatrix σ q E = B E* G⁻¹`, with the inverse written as
  `Ring.inverse G`. It gives polar coordinates relative to the rows of `E`.
- `complement σ q E = 1 - R E`, where `R = retractionMatrix σ q E`. This is
  the projection onto the polar orthogonal complement of `W`.
- `mul_retractionMatrix hE : E R = 1`.
- `complement_mul_polar_mul_adjoint hE : (1 - R E) B E* = 0` and
  `mul_polar_mul_adjoint_complement hE : E B (1 - R E)* = 0`. These say that
  the complement is polar-orthogonal to `W`.
- `sesqForm_complement_vecMul hE` and `sesqForm_projection_complement hE` state
  the same orthogonality for the sesquilinear form `σ.sesqForm (σ.polar q)` on
  vectors.
- `quadratic_decomposition hE` is the key identity

  `σ.quadraticPullback R (σ.quadraticPullback E q) + σ.quadraticPullback (1 - R E) q = q`.

  It holds for the quadratic class itself, not only for its polar form. The
  proof writes each vector as `v (R E) + v (1 - R E)` and applies
  `quadraticValue_add`; the cross term vanishes by the orthogonality above.
- `splitRepresentative σ q E` is the representative
  `R Q_W R* + (1 - R E) Q (1 - R E)*`, where `Q_W` and `Q` are the chosen
  representatives `Quotient.out` of `σ.quadraticPullback E q` and of `q`.
  `mk_splitRepresentative hE` shows that it represents `q`.

## The ambient group-scheme morphism (section `Scheme`)

This section follows the construction of `HyperbolicScheme.isometryHom`, with
`Fin 2` replaced by `k` and the plane inclusion and retraction replaced by `E`
and `R`.

- `inclusion E C` and `retraction σ q E C` are the coefficient extensions of
  `E` and `R` to `C ⊗[K] D`, for every commutative `K`-algebra `C`.
  `inclusion_mul_retraction hE C` shows that their product is still `1`.
- `extendUnits hE C` sends a unit `M` of `Matrix k k (C ⊗[K] D)` to the unit
  with matrix `R_C M E_C + (1 - R_C E_C)`, via `SplitMatrixExtension.unitsHom`.
  It is injective (`extendUnits_injective`) and natural in `C`
  (`extendUnits_naturality`).
- `scalarMatrix_splitRepresentative` computes the coefficient extension of
  `splitRepresentative`. `extendUnits_preserves hE` uses
  `SplitQuadraticExtension.defect_mem`: if `M` has alternating defect for the
  representative of `σ.quadraticPullback E q`, then the extended unit has
  alternating defect for the split representative of `q`, over every
  coefficient algebra.
- `pointMatrix`, `unitPoints` and `unitHom hE` give the matrix-unit
  group-scheme morphism
  `FiniteAlgebraUnits.groupScheme (Module.finBasis K (Matrix k k D)) ⟶
  FiniteAlgebraUnits.groupScheme (Module.finBasis K (Matrix n n D))`.
  It is built by `homOfPoints` from points on all relative test schemes `T`
  over `Spec K`, using `HyperbolicScheme.matrixPointsEquiv` with `C = Γ(T)`.
  `unitHom_points` gives its matrix formula.
- `isometryUnitHom hE` restricts `unitHom hE` to
  `σ.isometryGroup (σ.quadraticPullback E q)`. `isometryUnitHom_range_le hE`
  proves that its range lies in the range of the closed inclusion
  `σ.isometryGroupι q`. The proof uses the defining criterion
  `mem_range_isometryGroupι_iff`, once for the representative
  `Quotient.out (σ.quadraticPullback E q)` on the source and once for
  `splitRepresentative σ q E` on the target, together with
  `extendUnits_preserves`.
- `isometryHom hE : σ.isometryGroup (σ.quadraticPullback E q) ⟶ σ.isometryGroup q`
  is the resulting factorization through the closed inclusion. It satisfies
  `isometryHom_comp` (its composite with `σ.isometryGroupι q` is
  `isometryUnitHom hE`), the point formula `isometryHom_points` (the ambient
  matrix of the image of a point is `extendUnits hE` of its matrix), and
  `isometryHom_points_injective` (it is injective on points over every
  relative test scheme).

## Compatibility with a hyperbolic plane in the row space (section `Plane`)

- `value_value` is an identity of split extensions with no hypotheses:
  `value E R (value I S M) = value (I E) (R S) M`.
- `planeRetraction_eq_polar_mul` writes the plane retraction as a matrix
  product: `planeRetraction σ q e f = B (planeInclusion f e)*`.
- `isHyperbolicPair_single he hf h`: if `E i₀ = e`, `E i₁ = f`, and `e, f` is a
  hyperbolic pair of `q`, then the standard vectors `Pi.single i₀ 1` and
  `Pi.single i₁ 1` form a hyperbolic pair of `σ.quadraticPullback E q`.
- `planeInclusion_single_mul he hf`: `planeInclusion (Pi.single i₀ 1) (Pi.single i₁ 1) * E = planeInclusion e f`.
- `retractionMatrix_mul_planeRetraction hE he hf`: the retraction of the row
  space composed with the plane retraction of `σ.quadraticPullback E q` is the
  plane retraction of `q` for `e, f`. The proof uses `G⁻¹ G = 1`.
- `extendUnits_hyperbolic` combines these on unit matrices over every
  coefficient algebra.
- `hyperbolic_isometryHom_comp hE he hf h` is the group-scheme statement

  `HyperbolicScheme.isometryHom (isHyperbolicPair_single he hf h) ≫ isometryHom hE = HyperbolicScheme.isometryHom h`.

  The proof checks the identity on points over every relative test scheme,
  using that `σ.isometryGroupι q` is a monomorphism and that matrix
  coordinates are injective.

The indices `i₀` and `i₁` are arbitrary elements of `k`; no statement assumes
that they are distinct.

## Provenance

The construction is internal. It is the standard orthogonal splitting
`V = W ⊥ W^⊥` of a quadratic space along a nondegenerate subspace `W`,
expressed in matrix coordinates. An isometry of `W` is extended by the
identity on `W^⊥`. The module adapts the published hyperbolic-plane extension
`HyperbolicScheme.isometryHom` and reuses its matrix-point equivalence and
scalar-extension lemmas. It also uses the published split-matrix extension
(`SplitMatrixExtension`), the defect computation
`SplitQuadraticExtension.defect_mem`, and the represented isometry cut
`σ.isometryGroupι`. It asserts nothing about spin covers, kernels, elementary
generation or the Kneser–Tits property.
