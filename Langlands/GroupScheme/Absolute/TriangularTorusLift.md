# Correcting triangular lifts of split-torus points to homomorphisms

This module holds the core group-theoretic step of the proof of Milne 2017,
Theorem 16.26(a), in `Absolute/TriangularSplitExtension`. It works purely
with matrices, natural in the coefficient algebra. Suppose the points of a
split torus `G_m^I` have upper triangular lifts that are multiplicative and
normalizing modulo a unitriangular "kernel". Then, over an algebraically
closed field, one fixed unitriangular conjugate of the diagonal part of the
lift agrees with the lift modulo the kernel, at every point. That conjugate
is a homomorphism of `G_m^I` into `GL_N`. The namespace is
`Langlands.GroupScheme.TriangularLayer`. The filtration `W a`, `layer` and
the `Rel`/`Approx` calculus come from `Absolute/TriangularLayerFiltration`.

## Diagonal parts

- `diagPart A N : upper A N →* GL (Fin N) A` is the diagonal part of an upper
  triangular invertible matrix. It is defined as the published
  `GeneralLinear.blockLeviProjection` for the weights `i ↦ -i`, and
  `diagPart_apply` gives its entries.
- `diagPart_eq_one`: unitriangular matrices have diagonal part `1`.
  `inv_diagPart_mul_mem_W`: `(diagPart g)⁻¹ * g` is unitriangular.
  `map_diagPart` gives naturality in ring maps. `conj_apply_self`:
  conjugation by a unitriangular matrix keeps the diagonal entries.
- `exists_unitriangular`: over a field, every matrix `v` with `IsLevel a v`
  equals `z - 1` for some `z ∈ W a`, namely `z = 1 + v`.

## Laurent monomials

`laurentVar I A : I → (A[I → ℤ])ˣ` is the family of independent Laurent
monomials, the universal point of `G_m^I`. `laurentVar_scalars` says that
extending scalars from `k` to `A` carries `laurentVar I k` to
`laurentVar I A`. `laurentVar_translate` says that the published translation
`laurentTranslation I t` multiplies the universal family by the constant
family `t`.

## Lifts of torus points

`TorusLift k I N` is a structure. For every `k`-algebra `A` it has a lift
`lift A : (I → Aˣ) → GL_N(A)` and a subgroup `kernel A ≤ GL_N(A)`. The axioms
are:

- `lift_naturality`, `map_mem_kernel`: both are natural in `k`-algebra maps;
- `lift_mem_upper`: lifts are upper triangular;
- `kernel_le`: the kernel is unitriangular (`kernel A ≤ W A N 0`);
- `lift_mul_mem`: `(lift t * lift t')⁻¹ * lift (t * t') ∈ kernel`;
- `conj_mem`: the lifts normalize the kernel.

For such a lift `𝓛` and `x ∈ GL_N(k)`:

- `diagLift t` is the diagonal part of `lift t`. It is multiplicative
  (`diagLift_mul`), because the multiplicativity defect is unitriangular, and
  natural (`diagLift_naturality`).
- `correction x t = x⁻¹ · diagLift t · x`, with `x` viewed over `A`. It is a
  homomorphism in `t` (`correction_mul`, `correctionHom`) and natural
  (`correction_naturality`).
- `deviation x t = (correction x t)⁻¹ · lift t`. It is natural
  (`deviation_naturality`). `deviation_mul` writes the deviation at `t₁ t₂` in
  terms of the deviations at `t₁` and `t₂`, the conjugation by `lift t₂`, and
  the multiplicativity defect. This is a crossed-cocycle law modulo the
  kernel. `deviation_one_mem_W`: for `x = 1` the deviation is unitriangular.
  `scale_correction`: for unitriangular `x`, conjugation by the correction
  scales layers like conjugation by the lift.

## The averaging argument

Assume `k` is algebraically closed and `I` is finite.

- `layer_coeff_mem`: let `C` be a layer of the deviation at the universal
  family `laurentVar I k`, modulo the kernel at level `a`. Let `V` be a
  layer of the deviation at an arbitrary point `t` over `A`. Let `C₀` be the
  matrix of constant Laurent coefficients of `C`, extended to `A`, and let
  `L = layer a C₀`. Then `L - layer a V - scale(lift t⁻¹, lift t)(L)` lies in
  `layerGroup (kernel A) a`. Proof: over `R = A[I → ℤ]`, compare two expressions for the deviation
  at the translated universal family `laurentVar I A * t`. One comes from the
  cocycle law (`deviation_mul`, `Rel.mul`, `Rel.conj`). The other comes from
  naturality along `laurentTranslation`. `Rel.unique` shows that the two
  layers agree modulo `layerGroup (kernel R) a`. Their difference is a matrix
  of Laurent polynomials. All of its evaluations along `k`-algebra maps
  `R → A` lie in `layerGroup (kernel A) a`, by `layerGroup_map`. So
  `splitTorus.map_coeff_zero_mem` (module `Torus/LaurentRootAverage`) puts its
  constant coefficients there too. The constant coefficient is unchanged by
  translation (`coeff_zero_laurentTranslation`) and compatible with constants
  (`laurentConst`) and scalars (`laurentScalars`). A final entrywise
  computation identifies it with the displayed expression.
- `exists_approx_succ`: let `x` be unitriangular, and suppose the deviation
  of `x` lies in `kernel · W a` at every point. Take `C` for the universal
  family and let `z ∈ W k N a` be the matrix with `z - 1 = layer a C₀` over
  `k` (`exists_unitriangular`). Then the deviation of `x * z` lies in
  `kernel · W (a + 1)` at every point. The layer of the new deviation is the
  expression of `layer_coeff_mem` up to sign, so `Rel.approx_succ` applies.
- `exists_deviation_mem` (main result): some `x ∈ W k N 0` has
  `deviation x t ∈ kernel A` for all `A` and `t`. Proof: start from `x = 1`
  and apply `exists_approx_succ` `N` times. Then use `W A N N = 1`
  (`mem_of_approx_top`).

## Provenance

This is an internal construction. It replaces the induction along a
`D`-stable normal series in Milne's proof of Theorem 16.26 (Milne 2017,
pp. 332-333). It uses an induction along the superdiagonal filtration of a
triangular embedding instead. At each step the obstruction is a layer
cocycle with values in an additive group of matrices modulo the layers of the
kernel. It is killed by torus averaging (the constant Laurent coefficient),
which plays the role of `Ext¹(D, U) = 0` for algebraic subgroups `U` of `G_a`
(Milne 2017, Theorem 15.34(d)). The hypotheses are exactly the axioms of
`TorusLift`. The module itself mentions no group schemes.
