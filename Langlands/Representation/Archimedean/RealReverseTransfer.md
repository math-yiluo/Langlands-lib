# Transposing an intertwiner of real standard modules inside an `O(n)`-matrix coefficient

Lean module: `Langlands.Representation.Archimedean.RealReverseTransfer`.

Worker 5 wrote this module for Task 7069 (`79f2a631-6cbb-4805-97c7-163e69df5de3`), the proof of
`RealStandardIrreducibleCriterionStatement`. It is a helper for the reversal statement for
character lists with ties (`RealCharacterReverseKernel`). It moves an intertwiner `T` of real
standard modules from one side of an `O(n)`-matrix coefficient to the other: the pairing
`h ↦ ∫ v (T h)` is again a pairing `h ↦ ∫ u h` against a finite vector `u` of the dual principal
series, and then the whole matrix coefficients agree, `∫ (T w)(κ g) v(κ) dκ = ∫ w(κ g) u(κ) dκ`.

Notation: `GL_n(ℝ)` is `Langlands.GeneralLinear n ℝ`, `O(n)` is `unitaryCompact ℝ n` with the
Haar probability measure `RealPrincipalSeriesDuality.haarK n`. `R(k)` is
`Whittaker.rightTranslation ℂ _ k` (`R(k) f (x) = f(x k)`). `principalSeries ℝ n χ` is the
Library's smooth principal series of characters `χ_0, …, χ_{n−1}` of `ℝˣ`, and
`kFiniteFunctions V (unitaryCompact ℝ n)` the `O(n)`-finite functions of a space `V`. For a list
`ds` of real blocks, `I(ds) = kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)`
are the `O(n)`-finite functions of the standard module, a subspace of those of
`principalSeries ℝ n (realPositionCharacter ds)` (`realStandardModule_le_principalSeries`).
`dualChar χ` is the family `l, x ↦ (χ_l x)⁻¹`. `IsSignedPower χ e` (module
`PartialJacquetIntegral`) means `χ_l(x) = χ_l(sgn x) |x|^{e_l}`, `χ_l(1) = 1` and
`‖χ_l(−1)‖ = 1`. `IsRealStandardIntertwiner n ρ π ds T` (Library, `RealGenericParameterReduction`)
says that `T` commutes with right translation by `O(n)` and with all right derivatives.

Declarations without a prefix are in the namespace `Langlands.Archimedean.RealReverseTransfer`.
There is no statement (`def … : Prop`) in this module; it contains definitions and theorems only.

## Definitions

* `intPairing A B hA hB : A →ₗ[ℂ] B →ₗ[ℂ] ℂ`, for two spaces `A`, `B` of continuous functions on
  `GL_n(ℝ)`: the bilinear pairing `⟨a, b⟩ = ∫_{O(n)} a(κ) b(κ) dκ`. `intPairing_apply` unfolds it.

## Results

### Generalities

* `isFiniteVector_dual_of_equivariant`: let `L : W →ₗ[ℂ] Module.Dual ℂ V` be equivariant,
  `L (σ(k) w) = ρ^∨(k) (L w)`. Then `L` maps finite vectors of `σ` to finite vectors of the dual
  representation `ρ.dual`.
* `toUnits_mk`: the unitary-group element of `k ∈ O(n)` maps back to `k`.
* `mem_kFiniteFunctions_principalSeries`: `I(ds)` is contained in the `O(n)`-finite functions of
  `principalSeries ℝ n (realPositionCharacter ds)`.
* `integral_translate_mul`: for `k ∈ O(n)` and all functions `a, b`,
  `∫_{O(n)} a(κ k) b(κ) dκ = ∫_{O(n)} a(κ) b(κ k⁻¹) dκ`.

### Separation

`exists_integral_mul_ne_zero`. Let `IsSignedPower χ e`, and let `h ≠ 0` be an `O(n)`-finite
function of `principalSeries ℝ n χ`. Then some `O(n)`-finite function `u` of
`principalSeries ℝ n (dualChar χ)` satisfies `∫_{O(n)} u(κ) h(κ) dκ ≠ 0`.

### The pairing transpose

`exists_pairing_transpose`. Let `ds, ds'` be lists of real blocks, with
`IsSignedPower (realPositionCharacter ds) e`. Let `T : I(ds) →ₗ[ℂ] I(ds')` satisfy
`IsRealStandardIntertwiner n (realStandardRep n ds') (realStandardLie n ds') ds T`. Let `v` be an
`O(n)`-finite function of `principalSeries ℝ n (dualChar (realPositionCharacter ds'))`. Then there
is an `O(n)`-finite function `u` of `principalSeries ℝ n (dualChar (realPositionCharacter ds))`
with

`∫_{O(n)} u(κ) h(κ) dκ = ∫_{O(n)} v(κ) (T h)(κ) dκ` for every `h ∈ I(ds)`.

`exists_pairing_transpose_of_rep` is the same statement with the intertwiner hypothesis replaced
by `O(n)`-equivariance alone: `T (realStandardRep n ds k h) = realStandardRep n ds' k (T h)` for
all `k ∈ O(n)` and `h`. `exists_pairing_transpose` is derived from it
(`IsRealStandardIntertwiner.map_realStandardRep`).

`integral_mul_inv_swap`: let `IsSignedPower χ e`, `u ∈ principalSeries ℝ n (dualChar χ)` and
`w ∈ principalSeries ℝ n χ`. Then for every `g`,
`∫_{O(n)} w(κ g⁻¹) u(κ) dκ = ∫_{O(n)} u(κ g) w(κ) dκ`.

### Equality of matrix coefficients from equality at `1`

`matrixCoefficient_eq_of_rel`. Let `μ` be a finite measure on the unitary group, and write
`MatrixCoefficientAnalytic.matrixCoefficient μ f φ g = ∫ f(κ g) φ(κ) dμ(κ)`. Let `χ₁`, `χ₂` be
characters with `χᵢ_l(x) = χᵢ_l(sgn x) |x|^{eᵢ_l}`. Let `P` be a relation between functions on
`GL_n(ℝ)` such that

* `P a b` implies that `a` is an `O(n)`-finite function of `principalSeries ℝ n χ₁` and `b` one
  of `principalSeries ℝ n χ₂`;
* `P a b` implies `P (R(k) a) (R(k) b)` for `k ∈ O(n)`;
* `P a b` implies `P (rightDerivative X a) (rightDerivative X b)` for every real matrix `X`.

Let `φ₁, φ₂` be continuous on the unitary group. If
`matrixCoefficient μ a φ₁ 1 = matrixCoefficient μ b φ₂ 1` whenever `P a b`, then
`matrixCoefficient μ a φ₁ g = matrixCoefficient μ b φ₂ g` for all `g` whenever `P a b`.

### The transfer identity

`integral_mul_transfer`. Let `IsSignedPower (realPositionCharacter ds) e` and
`IsSignedPower (realPositionCharacter ds') e'`, and let `T : I(ds) →ₗ[ℂ] I(ds')` be an intertwiner
as above. Let `v` be `O(n)`-finite in `principalSeries ℝ n (dualChar (realPositionCharacter ds'))`
and `u` `O(n)`-finite in `principalSeries ℝ n (dualChar (realPositionCharacter ds))`, with
`∫ u h = ∫ v (T h)` over `O(n)` for every `h ∈ I(ds)`. Then for every `w ∈ I(ds)` and every
`g ∈ GL_n(ℝ)`

`∫_{O(n)} (T w)(κ g) v(κ) dκ = ∫_{O(n)} w(κ g) u(κ) dκ`.

Provenance. Derived, internal infrastructure. The ingredients are standard facts on
`(𝔤, K)`-modules: the `K`-finite dual of an admissible module is separated by a dual principal
series, and matrix coefficients of `K`-finite vectors are real analytic along `KAK`. The module
uses the Library's versions of these facts (`KFiniteDual.mem_of_separating`,
`MatrixCoefficientAnalytic.analyticAt_matrixCoefficient`, `exists_kak`) and makes no claim beyond
the Lean statements.

## Proof

`isFiniteVector_dual_of_equivariant`. The orbit span of `L w` is contained in the image under `L`
of the orbit span of `w`, which is finite-dimensional.

`integral_translate_mul`. Right invariance of the Haar measure on `O(n)`
(`integral_mul_right_eq_self`, with the local Borel instance `borelSpaceK_tr`) substitutes
`κ ↦ κ k`.

`exists_integral_mul_ne_zero`. Since `h ≠ 0` lies in a principal series, it does not vanish at
some `k₀ ∈ O(n)` (`exists_mem_unitaryCompact_ne_zero`). Let `φ = conj(h)` on the unitary group.
By `OrthogonalFinitePolynomial.exists_mvPolynomial_of_mem_kFiniteVectors`, `h` on `O(n)` is a
polynomial `P` in the matrix entries, so `φ` is the polynomial with conjugated coefficients. Then
the right translates of `φ` span a finite-dimensional space (`finiteDimensional_span_eval`). Also
`φ(m κ) = principalSeriesCharacter (dualChar χ) (sgn) · φ(κ)` for sign diagonal matrices `m`,
because `conj(χ_l(±1)) = χ_l(±1)⁻¹` (`‖χ_l(−1)‖ = 1`). Hence the extension `u` of `φ`
(`PrincipalSeriesExtension.extension_mem_kFiniteFunctions`, exponents `−e`) is an `O(n)`-finite
function of `principalSeries ℝ n (dualChar χ)` with `u = conj(h)` on `O(n)`
(`extension_unitary`). So `∫ u h = ∫ |h|²`, the integral of a continuous nonnegative function that
is positive at `k₀`; it is positive
(`Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero`).

`exists_pairing_transpose`. Let `S = I(ds)`, `S' = I(ds')`, `D` and `D'` the `O(n)`-finite
functions of the principal series of `dualChar (realPositionCharacter ds)` and of
`dualChar (realPositionCharacter ds')`. Put `Qd = intPairing D S : D → S^*` and
`Λ = (intPairing D' S') ∘ T : D' → S^*`. Both are `O(n)`-equivariant into the dual
representation of `realStandardRep n ds` (`integral_translate_mul`, and for `Λ` also the
`O(n)`-equivariance of `T`; this is the proof of `exists_pairing_transpose_of_rep`). The range `W'` of `Qd` is therefore a subrepresentation of the dual,
consisting of finite vectors (`isFiniteVector_dual_of_equivariant`, since `D` consists of finite
vectors). It separates `S`: if `h ∈ S` is nonzero, `exists_integral_mul_ne_zero` gives `u ∈ D`
with `Qd u h ≠ 0`. The real standard module is admissible with semisimple `O(n)`-action, so its
isotypic blocks are finite-dimensional (`KFiniteDual.finiteDimensional_block`,
`realStandardAdmissible`). Then `KFiniteDual.mem_of_separating` puts every finite vector of the
dual in `W'`, in particular the finite vector `Λ v`. So `Λ v = Qd u` for some `u ∈ D`, which is
the claim.

`integral_mul_inv_swap`. The function `x ↦ u(x g) w(x)` is smooth and modulus-equivariant,
because `(χ_l x)⁻¹ χ_l x = 1` (`isModulusEquivariant_mul`). The Library's
`kIntegralInvariance` at `g⁻¹` then says `∫ u(κ g⁻¹ g) w(κ g⁻¹) dκ = ∫ u(κ g) w(κ) dκ`. The
left-hand side is `∫ w(κ g⁻¹) u(κ) dκ`.

`matrixCoefficient_eq_of_rel`. First, along a diagonal one-parameter subgroup: suppose the two
matrix coefficients agree at `g` for all related pairs. The difference
`t ↦ matrixCoefficient a φ₁ (g exp(tH)) − matrixCoefficient b φ₂ (g exp(tH))` is real analytic,
with derivative the same difference for the pair `(rightDerivative H a, rightDerivative H b)`
(`analyticAt_matrixCoefficient`). That pair is again related. By induction on `j`, all iterated
derivatives at `t = 0` vanish. So the difference vanishes identically
(`eq_zero_of_iteratedDeriv_eq_zero`). Then for general `g = k₁ exp(H) k₂` (`exists_kak`):
`matrixCoefficient_mul_unitary` moves `k₂` into the functions (`R(k₂)`, related pairs stay
related), and agreement at `k₁` follows from agreement at `1` for `(R(k₁) a, R(k₁) b)`. The
one-parameter step from `k₁` to `k₁ exp(H)` concludes.

`integral_mul_transfer`. Apply `matrixCoefficient_eq_of_rel` with `μ` the image of `haarK n` on
the unitary group, `φ₁ = v`, `φ₂ = u`, and the relation `P a b :⇔ ∃ w', a = T w' ∧ b = w'`. It is
stable under `R(k)` and right derivatives because `T` is an intertwiner (`hT.map_realStandardRep`,
`hT.map_realStandardLie`). At `g = 1` the two coefficients are `∫ (T w') v` and `∫ w' u`, equal by
hypothesis. The matrix coefficients are the stated `O(n)`-integrals by
`integral_map_toUnitaryGroup`.
