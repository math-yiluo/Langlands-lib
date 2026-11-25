# The product reduction for minor vectors (Wallach's argument)

Lean module: `Langlands.Representation.Archimedean.RealTiedMinorProduct`, namespace
`Langlands.Archimedean.RealTiedMinorProduct`. The module serves the proof of
`Langlands.Archimedean.RealTemperedScalarCommutantStatement`.

## Purpose and provenance

Let `ds` be a list of real blocks without discrete-series block (`IsPrincipal ds`, module
`RealTiedMinorScalar`). Assume its odd positions `A = signSet n ds` form a bottom segment of
`{0, …, n-1}`. Write each odd character as `sgn·|·|^e = x·|·|^{e-1}`. Then every function of
the standard module is a sum `Σ_C Δ_{A,C} · h_C`. Here `Δ_{A,C}(g) = det g_{A,C}` and the
`h_C` lie in the spherical principal series of the even characters `|·|^{e_i - [i ∈ A]}`. This
module uses that decomposition to reduce cyclicity of the minor vectors to cyclicity of the
`O(n)`-fixed vector of that spherical principal series (`eq_top_of_sphCyclic`).

This is the method of the proof of Wallach (1971), Theorem 3.2 (printed p. 111; source
`wallach-1971-cyclic-vectors-principal-series`). There a vector built from an extension `V` of
the `M`-type is the product of the spherical vector `1_γ` with a matrix-coefficient function
`α(v)`. Kostant's theorem makes `1_γ` cyclic, so the closed invariant subspace contains
`(U(𝔤) 1_γ) · α(v)`. Its restrictions to `K` span `C(K, δ)`. The Lean module is an algebraic
version for `GL_n(ℝ)` with `V = Λ^{|A|} ℂ^n`:

* it works with `O(n)`-finite functions and subspaces stable under the Lie algebra, with no
  closures;
* `α(v)` becomes the minor functions `Δ_{A,C}`;
* the partition-of-unity step becomes the identity `Σ_C det(κ_{A,C})² = 1` on `O(n)`;
* the cyclicity of the spherical vector is a hypothesis of the main theorem (`hcyc`), not
  Kostant's theorem.

The module makes no other literature claim.

## Notation

As in `RealTiedMinorScalar.md`: `KF n ds`, `realStandardRep`, `realStandardLie`,
`signSet n ds`, `vec hds B = φ_{A,B}`. `minorFun n A B` (Library `JacquetMinorNonvanishing`) is
`κ ↦ det κ_{A,B}` on `O(n)`. `extension e φ` (Library `PrincipalSeriesExtension`) extends a
function `φ` on `O(n)` to the principal series with exponents `e` by the Iwasawa
decomposition.

## Definitions

* `minorG A B g = det g_{A,B}` on `GL_n(ℝ)`, as a complex function.
* `IsBottom R`: `R` is closed upwards, i.e. `i ≤ j` and `i ∈ R` imply `j ∈ R`.
* `shiftExp n ds R i = realPositionExponent ds i - [i ∈ R]`.
* `sphList n ds R`: the list of the even characters `|·|^{shiftExp n ds R i}`, `i < n`
  (built with the Library's `RealJacquetFrobenius.charData 0`). `sphBlocks n ds R` is that list
  as real blocks.
* `mulMinor hds hR C : KF n (sphBlocks n ds A) →ₗ[ℂ] KF n ds`, the map `h ↦ Δ_{A,C} · h`.
* `pullback hds hR W`: for a subspace `W` of `KF n ds`, the `h` in the spherical module with
  `Δ_{A,C} h ∈ W` for every `C`.
* `sphVec R`: the `O(n)`-fixed vector of the spherical module, equal to `1` on `O(n)`.
* `coef f R C`: the function `κ ↦ f(κ) · det κ_{R,C}` on `O(n)`. `coefVec f C` is its extension
  to the spherical module (the coefficient `h_C`).

## Results

Minor functions.

* `contDiff_minor`, `contMDiff_minorG`: minors are smooth.
* `minorG_mul` (Cauchy–Binet): `Δ_{A,B}(g g') = Σ_{|C|=|A|} Δ_{A,C}(g) det g'_{C,B}`.
* `minor_upper_mul`, `minorG_borel_mul`: if `b` is upper triangular and `R` a bottom segment,
  then `Δ_{R,C}(b g) = (Π_{i ∈ R} b_ii) Δ_{R,C}(g)`.
* `minorG_mem_kFiniteVectors`, `mul_mem_kFiniteVectors`, `finiteDimensional_translateSpan_mul`,
  `finiteDimensional_restrict`: minors are `O(n)`-finite, and products of `O(n)`-finite
  functions are `O(n)`-finite.
* `rightDerivative_minorG`: the right derivative of `Δ_{R,C}` along `X` is a combination
  `Σ_D c_D Δ_{R,D}` (differentiate Cauchy–Binet).

Characters.

* `posChar_eq`, `principalSeriesCharacter_eq_mul`, `sphChar_sign`: the character of `ds` at
  position `i` is the shifted spherical character times `x ↦ x^{[i ∈ A]}`.
* `mul_minorG_mem`, `mulMinor`: so `Δ_{A,C} h` lies in `KF n ds` for `h` in the spherical module
  (`mem_KF_iff` uses `realStandardModule_eq`).

The pullback is Lie-stable.

* `mulMinor_lie` (product rule):
  `Δ_C · R(X) h = R(X)(Δ_C h) - Σ_D c_D Δ_D h`.
* `pullback_lie`: if `W` is stable under `realStandardLie n ds`, then `pullback W` is stable
  under the Lie algebra of the spherical module. A general element `Z` is a sum of
  `z ⊗ X`, and the product rule applies to each.
* `sphVec_fixed`, `sphVec_ne_zero`, `mulMinor_sphVec`: `sphVec` is `O(n)`-fixed and nonzero.
  `Δ_{A,C} · sphVec = φ_{A,C}`: both are in the principal series and agree on `O(n)`.

Spanning.

* `coef_signDiagonal`, `coef_mem`: `coef f A C` has the sign law of the spherical module, so it
  extends to an element `coefVec f C`.
* `sum_minor_sq`: `Σ_{|C|=|R|} det(κ_{R,C})² = 1` for `κ ∈ O(n)` (Cauchy–Binet for
  `κ κᵀ = 1`).
* `sum_mulMinor_coefVec`: every `f ∈ KF n ds` is `Σ_C Δ_{A,C} · coefVec f C`. Both sides are in
  the principal series. On `O(n)` the right side is `f(κ) Σ_C det(κ_{A,C})² = f(κ)`.

Main theorem.

* `eq_top_of_sphCyclic`: assume `IsPrincipal ds`, `IsBottom (signSet n ds)`, and `hcyc`: every
  Lie-stable subspace of the spherical module containing `sphVec` is everything. Let `W` be a
  Lie-stable subspace of `KF n ds` containing every `φ_{A,B}` with `|B| = |A|`. Then `W = ⊤`.
  Proof: `pullback W` is Lie-stable (`pullback_lie`) and contains `sphVec` (`mulMinor_sphVec`),
  so it is everything by `hcyc`. Hence `Δ_{A,C} h ∈ W` for every `h` and `C`, and
  `sum_mulMinor_coefVec` writes any `f` as a sum of such products.
