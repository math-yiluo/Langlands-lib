# Slices along the tied block: finite decomposition and density

Lean module: `Langlands.Representation.Archimedean.ComplexBlockSlice`.

This module is a
helper for the proof of `ComplexReverseIntertwinerKernelStatement` at tied exponents (the route of
`ComplexReverseIntertwinerTied`, through `ComplexReverseBlockRecursion`). It imports the Library
module `ComplexBlockDual`.

Notation as in `ComplexBlockDual`: `GL_N(ℂ)` is `Langlands.GeneralLinear N ℂ`, `U(N)` is
`unitaryCompact ℂ N`, `diag(g₁, g₂)` is `blockDiagGL g₁ g₂` and `R(g)` is right translation
`Whittaker.rightTranslation` (`R(g) u (x) = u(x g)`). `dualChar χ` is `(l, z) ↦ (χ_l z)⁻¹`, and
`IsPhasePower χ e` comes from `ComplexPartialJacquet`. `restrictBlock u (g₁) = u(diag(g₁, 1))`,
`sliceFun κ₁ u (g₂) = u(diag(κ₁, g₂))`, `blockShiftChar` and
`blockDualChar a χ l z = χ_{a+l}(z)⁻¹ (|z|²)^{-a/2}` are from `ComplexBlockDual` and
`ComplexBlockJacquet`. "`U(N)`-finite function of the principal series of `ψ`" means an element of
`kFiniteFunctions (principalSeries ℂ N ψ) (unitaryCompact ℂ N)`. Unprefixed names below are in the
namespace `Langlands.Archimedean.ComplexBlockSlice`.

## Results

* `exists_finsupp_eval` (linear algebra). Let `W` be a finite-dimensional space of functions
  `Y → ℂ` and `K ⊆ Y` a set such that every `w ∈ W` vanishing on `K` is zero. Then every linear
  functional `f` on `W` is a finite combination of evaluations at points of `K`: there is a finitely
  supported `c : Y →₀ ℂ` with support in `K` and `f(w) = ∑_{y ∈ supp c} c(y) w(y)` for all `w ∈ W`.
* `restrictBlock_mem_principalSeries`. Assume `IsPhasePower χ e`. If `u` lies in the principal
  series of `χ⁻¹` on `GL_{a+k+1}(ℂ)`, then `g₁ ↦ u(diag(g₁, 1))` lies in the principal series of
  `(blockShiftChar k χ)⁻¹` on `GL_a(ℂ)`. No finiteness of `u` is assumed (this differs from
  `ComplexBlockDual.restrictBlock_mem`, which also gives `U(a)`-finiteness for `U(a+k+1)`-finite
  `u`).
* `blockDiag_eq_of_eqOn_unitary`. Assume `IsPhasePower χ e`. If `v, w` lie in the principal series
  of `χ⁻¹` and `v(diag(κ₁, 1)) = w(diag(κ₁, 1))` for every `κ₁ ∈ U(a)`, then
  `v(diag(g₁, 1)) = w(diag(g₁, 1))` for every `g₁ ∈ GL_a(ℂ)`.
* `exists_blockDiag_decomposition` (finite decomposition). Assume `IsPhasePower χ e` and
  `χT_l(z) = blockDualChar a χ l z` for `l < k+1` and all `z`. Let `u` be a `U(a+k+1)`-finite
  function of the principal series of `χ⁻¹`. Then there are `d ∈ ℕ`, functions `p_0, …, p_{d−1}` on
  `GL_{a+k+1}(ℂ)` and functions `φ_0, …, φ_{d−1}` on `GL_{k+1}(ℂ)` such that
  * each `p_i` is a `U(a+k+1)`-finite function of the principal series of `χ⁻¹`;
  * each `p_i` lies in the linear span of the translates `R(κ) u`, `κ ∈ U(a+k+1)`;
  * each `φ_i` is a `U(k+1)`-finite function of the principal series of `χT`;
  * `u(diag(g₁, g₂)) = ∑_{i<d} p_i(diag(g₁, 1)) φ_i(g₂)` for all `g₁ ∈ GL_a(ℂ)` and
    `g₂ ∈ GL_{k+1}(ℂ)`.
* `exists_mem_blockDiag_eq` (density). Assume `IsPhasePower χ e`, `χT_l = blockDualChar a χ l`
  for `l < k+1`, and that the `(𝔤𝔩_{k+1}(ℂ), U(k+1))`-module
  `(principalSeriesRep ℂ (k+1) χT, principalSeriesLie ℂ (k+1) χT)` is irreducible
  (`IsIrreducibleGKModule`). Let `U` be a subspace of the `U(a+k+1)`-finite functions of the
  principal series of `χ⁻¹`, stable under `R(κ)` for every `κ ∈ U(a+k+1)` and under the right
  derivative `rightDerivative (matrixModel ℂ (a+k+1)) X` for every complex matrix `X`. Then for
  every `u ∈ U` and every `U(k+1)`-finite function `φ` of the principal series of `χT` there is
  `u' ∈ U` with `u'(diag(g₁, g₂)) = u(diag(g₁, 1)) φ(g₂)` for all `g₁ ∈ GL_a(ℂ)` and
  `g₂ ∈ GL_{k+1}(ℂ)`.

The order hypotheses on the exponents `e` (as in `ComplexBlockLimit`) are not needed here.

Provenance. Derived (internal). `exists_mem_blockDiag_eq` is steps 1–4 of the proof of
`ComplexBlockDual.integral_restrictBlock_mul_blockPair_eq_zero`, stated as a lemma of
its own and extended from unitary `g₁, g₂` to all of `GL_a(ℂ) × GL_{k+1}(ℂ)`.
`exists_blockDiag_decomposition` is the same slice argument with Jacobson density replaced by
elementary linear algebra (a basis of the finite-dimensional space of slices and
`exists_finsupp_eval`). No literature statement is claimed, and the Markdown claims nothing beyond
the Lean statements.

## Proof

* `exists_finsupp_eval`. Let `ev_y ∈ W*` be evaluation at `y`. A vector of `W` killed by all `ev_y`,
  `y ∈ K`, vanishes on `K` and so is zero. Hence the dual coannihilator of
  `span{ev_y : y ∈ K}` is `0`. In finite dimension `Subspace.dualCoannihilator_dualAnnihilator_eq`
  turns this into `span{ev_y : y ∈ K} = W*`. So `f` lies in this span, and
  `Finsupp.mem_span_image_iff_linearCombination` gives `c` supported in `K` with
  `f = ∑_y c(y) ev_y`. Evaluating at `w` gives the formula.
* `restrictBlock_mem_principalSeries`. Smoothness is `ComplexBlockDual.contMDiff_restrictBlock`. For
  the equivariance, write
  `diag(t v g, 1) = t'' · diag(v, 1) · diag(g, 1)`, with `t = diagonalUnits z`, `v` upper unipotent,
  `t'' = diagonalUnits (z, 1, …, 1)` and `diag(v, 1)` upper unipotent
  (`blockDiagGL_diagonalUnits`, `blockDiagGL_mem_upperUnipotent`, `blockDiagGL_mul`). The
  equivariance of `u` and `principalSeriesCharacter_addCases_dual` (the character of `χ⁻¹` at
  `(z, 1, …, 1)` is the `GL_a` character of `(blockShiftChar k χ)⁻¹` at `z`) give the claim.
* `blockDiag_eq_of_eqOn_unitary`. By the previous lemma `restrictBlock (v − w)` lies in a principal
  series of `GL_a(ℂ)` and vanishes on `U(a)`. A principal-series function vanishing on the unitary
  group is zero (`ComplexDuality.eq_zero_of_mem_principalSeries_of_eqOn`, Iwasawa decomposition).
  Evaluate at `g₁`.
* `exists_blockDiag_decomposition`.
  1. Let `V` be the span of the translates `R(κ) u`, `κ ∈ U(a+k+1)`. It is finite-dimensional
     because `u` is `U(a+k+1)`-finite (`mem_kFiniteVectors_iff`), and it consists of
     `U(a+k+1)`-finite functions of the principal series of `χ⁻¹`
     (`rightTranslation_mem_kFiniteFunctions_principalSeries`).
  2. Let `W = sliceFun 1 (V)`, finite-dimensional. Its elements are `U(k+1)`-finite functions of the
     principal series of `χT` (`ComplexBlockDual.sliceFun_mem`), so they are determined by their
     values on `U(k+1)`. For `κ₁ ∈ U(a)`, `sliceFun κ₁ u = sliceFun 1 (R(diag(κ₁, 1)) u) ∈ W`
     (`sliceFun_eq_sliceFun_one`).
  3. Take a basis `b_0, …, b_{d−1}` of `W` (`Module.finBasis`). By `exists_finsupp_eval` (with
     `K = U(k+1)`) the `i`-th coordinate functional is `w ↦ ∑_y c_i(y) w(y)` with `c_i` supported in
     `U(k+1)`. Put `φ_i = b_i` and `p_i = ∑_{y} c_i(y) R(diag(1, y)) u`. Each `diag(1, y)` is
     unitary, so `p_i ∈ V`.
  4. For unitary `κ₁` and any `g₂`, expand `sliceFun κ₁ u ∈ W` in the basis
     (`Module.Basis.sum_repr`) and evaluate at `g₂`:
     `u(diag(κ₁, g₂)) = ∑_i coord_i(sliceFun κ₁ u) b_i(g₂)`. The coefficient is
     `∑_y c_i(y) u(diag(κ₁, y)) = ∑_y c_i(y) u(diag(κ₁, 1) diag(1, y)) = p_i(diag(κ₁, 1))`.
  5. For general `g₁` fix `g₂` and apply `blockDiag_eq_of_eqOn_unitary` to
     `v = R(diag(1, g₂)) u` and `w = ∑_i φ_i(g₂) p_i`, both in the principal series of `χ⁻¹`
     (`rightTranslation_mem_principalSeries`). They agree on `diag(κ₁, 1)`, `κ₁ ∈ U(a)`, by step 4
     and `diag(κ₁, g₂) = diag(κ₁, 1) diag(1, g₂)` (`blockDiagGL_mul`). Evaluating at `diag(g₁, 1)`
     gives the decomposition.
* `exists_mem_blockDiag_eq`.
  1. As in steps 1–2 above, all slices `sliceV κ₁ u` (`κ₁ ∈ U(a)`) lie in the preimage `S` of `W`
     in the `U(k+1)`-finite principal series of `χT`. `S` is finite-dimensional (it injects into
     `W`), so it has a finite spanning set `s` (`Submodule.fg_iff_finiteDimensional`).
  2. Let `f(v) = v(1) · φ` (`kFiniteEval`, `LinearMap.smulRight`). By
     `ComplexBlockDual.hyp_principalSeries` the irreducible principal series of `χT` satisfies the
     hypotheses of `GKModuleDensity.exists_freeAlgebra_eq`, which gives `A` in the free algebra on
     the generators with `A · v = f(v)` for `v ∈ s`, hence for `v ∈ S` (`LinearMap.eqOn_span`).
  3. `ComplexBlockDual.exists_sliceV_eq` gives `u' ∈ U` with `sliceV κ₁ u' = A · sliceV κ₁ u` for
     every `κ₁`. For unitary `κ₁` and any `g₂` this reads
     `u'(diag(κ₁, g₂)) = u(diag(κ₁, 1)) φ(g₂)`.
  4. The extension to all `g₁` is step 5 above with `v = R(diag(1, g₂)) u'` and `w = φ(g₂) · u`.
