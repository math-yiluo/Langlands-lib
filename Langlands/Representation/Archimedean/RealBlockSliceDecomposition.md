# Slices of principal-series functions along `P_{a,k+1}` of `GL_{a+k+1}(ℝ)`

Lean module: `Langlands.Representation.Archimedean.RealBlockSliceDecomposition`.

Worker 5 wrote this module for Task 7069 (`79f2a631-6cbb-4805-97c7-163e69df5de3`), the proof of
`RealStandardIrreducibleCriterionStatement`. It is a helper for the reversal statement for
character lists with ties (`RealCharacterReverseKernel`, through `RealReverseRecursion`). It
extends two pieces of Worker 5220's module `RealBlockDual` (Task 6749) from the block
`h ∈ O(a)` to all `h ∈ GL_a(ℝ)`:

* a finite separation of variables `y(diag(h, g₂)) = ∑ᵢ ỹᵢ(diag(h, 1)) bᵢ(g₂)`;
* the density step: inside a `(𝔤, K)`-stable space containing `x`, there is a function equal
  to `x(diag(h, 1)) φ(g₂)` on all block-diagonal matrices `diag(h, g₂)`.

Notation: `GL_N(ℝ)` is `Langlands.GeneralLinear N ℝ`, `O(N)` is `unitaryCompact ℝ N`,
`diag(g₁, g₂)` is `blockDiagGL g₁ g₂` (block-diagonal matrix in `GL_{a+(k+1)}(ℝ)`), `R(g)` is
`Whittaker.rightTranslation ℂ _ g` (right translation, `R(g) y (x) = y(x g)`). From
`RealBlockDual`: `sliceFun g₁ y = (g₂ ↦ y(diag(g₁, g₂)))` and
`restrictBlock y = (g₁ ↦ y(diag(g₁, 1)))` (both `ℂ`-linear),
`blockDualChar a χ l z = (χ_{a+l}(z))⁻¹ |z|^{−a/2}` (the characters of the principal series of
the tied block that contains the slices of functions in the principal series of `χ⁻¹`). The
principal series `principalSeries ℝ N ψ` and its `O(N)`-finite part
`kFiniteFunctions (principalSeries ℝ N ψ) (unitaryCompact ℝ N)` are the Library's.
`IsSignedPower χ e` (module `PartialJacquetIntegral`) means `χ_l(x) = χ_l(sgn x) |x|^{e_l}`,
`χ_l(1) = 1` and `‖χ_l(−1)‖ = 1`; `dualChar χ` is `l, x ↦ (χ_l x)⁻¹`.

Declarations without a prefix are in the namespace
`Langlands.Archimedean.RealBlockSliceDecomposition`. There is no statement (`def … : Prop`) in
this module; it contains definitions and theorems only.

## Results

### Interpolation

* `exists_interpolation_of_separating`: let `S` be a finite-dimensional `ℂ`-subspace of functions
  `X → ℂ` and `P ⊆ X` such that every `s ∈ S` vanishing on `P` is zero. Then there are a finite
  type `ι`, points `p i ∈ P` and functions `u i ∈ S` with `s = ∑ᵢ s(p i) • u i` for every
  `s ∈ S`.

### The slice space

* `transSpan y` is the span of the right translates `R(κ) y`, `κ ∈ O(a+k+1)`.
* `sliceSpace y` is the image of `transSpan y` under `sliceFun 1`, i.e. the space of functions
  `g₂ ↦ v(diag(1, g₂))` with `v ∈ transSpan y`.
* `finiteDimensional_transSpan`, `finiteDimensional_sliceSpace`: for `y` an `O(a+k+1)`-finite
  function of a principal series, both spaces are finite-dimensional.
* `transSpan_le`: for such `y`, `transSpan y` consists of `O(a+k+1)`-finite functions of the same
  principal series.
* `sliceSpace_le`: if `IsSignedPower χ e`, `χT l z = blockDualChar a χ l z` for `l < k + 1`, and
  `y` is an `O(a+k+1)`-finite function of the principal series of `χ⁻¹`, then `sliceSpace y`
  consists of `O(k+1)`-finite functions of `principalSeries ℝ (k+1) χT`.
* `sliceFun_mem_sliceSpace`: if `y` is in some principal series `principalSeries ℝ (a+k+1) ψ`,
  then for every `h ∈ GL_a(ℝ)` the slice `sliceFun h y` lies in `sliceSpace y`.

### Separation of variables

`exists_blockDiag_decomposition`: assume `IsSignedPower χ e`, `χT l z = blockDualChar a χ l z` for
`l < k + 1`, and `y` an `O(a+k+1)`-finite function of the principal series of `χ⁻¹`. Then there
are a finite type `ι`, functions `ỹᵢ` (`yt i`), `O(a+k+1)`-finite in the principal series of
`χ⁻¹`, and functions `bᵢ`, `O(k+1)`-finite in `principalSeries ℝ (k+1) χT`, such that for all
`h ∈ GL_a(ℝ)` and `g₂ ∈ GL_{k+1}(ℝ)`

`y(diag(h, g₂)) = ∑ᵢ restrictBlock ỹᵢ h · bᵢ(g₂) = ∑ᵢ ỹᵢ(diag(h, 1)) bᵢ(g₂)`.

### Density on the tied block

`exists_mem_blockDiag_eq`: assume `IsSignedPower χ e`, `χT l z = blockDualChar a χ l z` for
`l < k + 1`, and that `principalSeries ℝ (k+1) χT` is irreducible as a `(𝔤, K)`-module
(`IsIrreducibleGKModule (principalSeriesRep ℝ (k+1) χT) (principalSeriesLie ℝ (k+1) χT)`). Let
`X` be a space of `O(a+k+1)`-finite functions of the principal series of `χ⁻¹`, stable under right
translation by `O(a+k+1)` and under right derivatives `rightDerivative (matrixModel ℝ (a+k+1)) Y`
for all real matrices `Y`. Then for every `x ∈ X` and every `O(k+1)`-finite `φ` of
`principalSeries ℝ (k+1) χT` there is `x' ∈ X` with

`x'(diag(h, g₂)) = x(diag(h, 1)) · φ(g₂)` for all `h ∈ GL_a(ℝ)`, `g₂ ∈ GL_{k+1}(ℝ)`.

Provenance. Derived, internal infrastructure. The separation of variables is elementary linear
algebra plus the Iwasawa decomposition. The density step is the Jacobson density theorem for
irreducible admissible `(𝔤, K)`-modules (Library `GKModuleDensity`), applied as in
`RealBlockDual.integral_restrictBlock_mul_blockPair_eq_zero`. The module makes no claim beyond the
Lean statements.

## Proof

`exists_interpolation_of_separating`. Take a basis `b` of `S`. Each coordinate functional
`b.coord j` extends to a linear functional `ℓ` on all functions (`LinearMap.exists_extend`). The
point evaluations at points of `P` separate `S`, so by the Library lemma
`exists_sum_of_separating` (module `PrincipalSeriesGKModule`) `ℓ` agrees on `S` with a finite
combination `∑ᵢ cᵢ s(pᵢ)`. Index by pairs `(j, i)`: put `p_{(j,i)} = p_{j,i}` and
`u_{(j,i)} = c_{j,i} b_j`. Then `s = ∑_j b.coord j s · b_j = ∑_{(j,i)} s(p_{j,i}) c_{j,i} b_j`.

`finiteDimensional_transSpan` is the definition of `O(N)`-finiteness
(`mem_kFiniteVectors_iff`), and `finiteDimensional_sliceSpace` follows because the image of a
finite-dimensional space is finite-dimensional. `transSpan_le`: right translates of an
`O(N)`-finite function of a principal series by elements of `O(N)` stay in it
(`rightTranslation_mem_kFiniteFunctions_principalSeries`). `sliceSpace_le` is
`RealBlockDual.sliceFun_mem` applied to elements of `transSpan y`.

`sliceFun_mem_sliceSpace`. Write `h = z u κ` (Iwasawa decomposition,
`exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact`: `z` diagonal, `u` upper unipotent,
`κ ∈ O(a)`). Then `diag(h, g₂) = diag(z, 1) · diag(u, 1) · diag(κ, g₂)`, where `diag(z, 1)` is
diagonal and `diag(u, 1)` upper unipotent. So the equivariance of `y` gives
`sliceFun h y = c · sliceFun κ y` with `c` the value of the principal-series character at
`diag(z, 1)`. Finally `sliceFun κ y = sliceFun 1 (R(diag(κ, 1)) y)`
(`RealBlockDual.sliceFun_eq_sliceFun_one`), and `diag(κ, 1) ∈ O(a+k+1)`, so this is in
`sliceSpace y`.

`exists_blockDiag_decomposition`. The slice space is finite-dimensional, and its elements are in
a principal series, so an element vanishing on `O(k+1)` is zero
(`eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact`). Interpolation gives points
`pᵢ ∈ O(k+1)` and `bᵢ = uᵢ ∈ sliceSpace y` with `s = ∑ᵢ s(pᵢ) bᵢ` on the slice space. Take
`ỹᵢ = R(diag(1, pᵢ)) y`; it is `O(a+k+1)`-finite in the principal series of `χ⁻¹`
(`diag(1, pᵢ) ∈ O(a+k+1)`), and `bᵢ` is `O(k+1)`-finite in the tied principal series by
`sliceSpace_le`. Apply the interpolation identity to the slice `sliceFun h y` (in the slice space
by `sliceFun_mem_sliceSpace`) and evaluate at `g₂`:
`y(diag(h, g₂)) = ∑ᵢ y(diag(h, pᵢ)) bᵢ(g₂)`, and
`y(diag(h, pᵢ)) = y(diag(h, 1) diag(1, pᵢ)) = ỹᵢ(diag(h, 1))`.

`exists_mem_blockDiag_eq`. This repeats the density argument of
`RealBlockDual.integral_restrictBlock_mul_blockPair_eq_zero`, with the slice space of `x` in place
of the span of the slices at `κ₁ ∈ O(a)`. Let `W = sliceSpace x` (finite-dimensional) and `S` the
corresponding subspace of the `O(k+1)`-finite functions of the tied principal series. By
`sliceFun_mem_sliceSpace`, every slice `RealBlockDual.sliceV … h x` (`h ∈ GL_a(ℝ)`) lies in `S`.
Let `f` be the rank-one endomorphism `v ↦ v(1) φ` (`(kFiniteEval _ 1).smulRight φ`). Since the
tied principal series is irreducible (and admissible; `RealBlockDual.hyp_principalSeries`), the
density theorem `GKModuleDensity.exists_freeAlgebra_eq`, applied to a finite spanning set of `S`,
gives an element `A` of the free algebra on the generators (elements of `O(k+1)` and of
`ℂ ⊗ 𝔤𝔩_{k+1}(ℝ)`) that acts as `f` on `S`. By `RealBlockDual.exists_sliceV_eq` (using that `X` is
stable under `O(a+k+1)` and under right derivatives) there is `x' ∈ X` whose slice at every `h`
is `A` applied to the slice of `x` at `h`. Evaluating at `g₂`:
`x'(diag(h, g₂)) = (A · sliceFun h x)(g₂) = (f (sliceFun h x))(g₂) = x(diag(h, 1)) φ(g₂)`.
