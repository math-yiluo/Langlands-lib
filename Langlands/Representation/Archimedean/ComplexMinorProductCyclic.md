# Cyclicity of products with minor monomials

Lean module: `Langlands.Representation.Archimedean.ComplexMinorProductCyclic`.

This module is the product lemma of the proof of the Library statement
`ComplexTemperedStandardIrreducibleStatement` (module `ComplexTemperedStandardIrreducibleProof`).
In that proof the vector `f₀` produced here is fed into the Library theorem
`complexTemperedIrreducible_of_minorMonomial` (module `ComplexLowestKTypeMultOne`), whose
hypothesis `hcyc` has exactly the cyclicity form of the conclusion below.

Notation. For a list `ds` of complex characters, `X(ds)` is the `(𝔤𝔩_n(ℂ), U(n))`-module of
`U(n)`-finite functions of `complexStandardModule n ds` (the principal series of the position
characters `complexPositionCharacter ds i`), with `U(n)` acting by
`complexStandardRep n ds` (right translation) and `ℂ ⊗_ℝ 𝔤𝔩_n(ℂ)` acting by
`complexStandardLie n ds` (right derivatives). A vector `f` of `X(ds)` is *cyclic* if every
subspace of `X(ds)` that is stable under `complexStandardRep n ds k` for all `k ∈ U(n)` and
under `complexStandardLie n ds Z` for all `Z ∈ ℂ ⊗_ℝ 𝔤𝔩_n(ℂ)` and contains `f` is all of `X(ds)`.
`minorMonomial c d g = det(g)^d · ∏_j Δ_{j+1}(g)^{c_j}` (Library, `ComplexLowestKType`), where
`Δ_{j+1}` is the minor on the bottom `j + 1` rows and the first `j + 1` columns, and
`ComplexMinorProduct.minorWeight c d i = d + ∑_{j : n − (j + 1) ≤ i} c_j` is defined in the
helper module `ComplexMinorMonomialCalculus`.

## The statement

`Langlands.Archimedean.ComplexMinorProductCyclicStatement`: for every `n`, lists `ds`, `ds'`
of complex characters, `c : Fin n → ℕ` and `d : ℤ`, assume

* `hχ`: `complexPositionCharacter ds i z = z^{minorWeight c d i} · complexPositionCharacter ds' i z`
  for every position `i : Fin n` and every `z ∈ ℂˣ`;
* `T` is a vector of `X(ds')` fixed by `complexStandardRep n ds' k` for every `k ∈ U(n)`;
* `T` is cyclic in `X(ds')`.

Then there is a vector `f₀` of `X(ds)` with `f₀(g) = minorMonomial c d g · T(g)` for every
`g ∈ GL_n(ℂ)`, and `f₀` is cyclic in `X(ds)`.

No length hypothesis on `ds`, `ds'` is needed. It is proved here as
`Langlands.Archimedean.complexMinorProductCyclic`, with no hypotheses.

Provenance. This is an internal lemma of the tempered-irreducibility route. Multiplying a
spherical vector by a lowest-`U(n)`-type polynomial to move between principal series, and
Godement's argument that a nonzero function in a principal series cannot be orthogonal to
all translates of the products, are standard tools. This exact formulation is ours.

## Further exported results (namespace `Langlands.Archimedean.ComplexMinorProduct`)

For a `(𝔤𝔩_n(ℂ), U(n))`-module `(ρ, π)` on a complex vector space `V` (any Lie action
`π : ℂ ⊗_ℝ 𝔤𝔩_n(ℂ) → End V` for the first five, and the Library predicate
`IsComplexGKModule n ρ π` where stated):

* `upperClosure π v`: the smallest subspace containing `v` and stable under `π(1 ⊗ X)` for every
  upper triangular `X`. With `mem_upperClosure_self`, `upper_mem_upperClosure`,
  `upperClosure_le` (it is contained in every subspace with these two properties).
* `lie_mem_upperClosure`, `lieAll_mem_upperClosure`: if `π(1 ⊗ Y) v = 0` for every
  skew-Hermitian `Y`, then `upperClosure π v` is stable under `π(1 ⊗ Y)` for every `Y`, and
  under `π Z` for every `Z ∈ ℂ ⊗_ℝ 𝔤𝔩_n(ℂ)`.
* `lie_skew_eq_zero` (`IsComplexGKModule`): a `U(n)`-fixed vector is killed by `π(1 ⊗ Y)` for
  every skew-Hermitian `Y`.
* `rho_mem_upperClosure` (`IsComplexGKModule`): for a `U(n)`-fixed `v`, `upperClosure π v` is
  `U(n)`-stable.
* `upperClosure_eq_top` (`IsComplexGKModule`): for a `U(n)`-fixed cyclic `v`,
  `upperClosure π v = ⊤`.

For the standard modules:

* `MKF n ds`: the `U(n)`-finite functions of `complexStandardModule n ds`, as a submodule.
* `principalSeriesCharacter_eq_prod_mul`: if `χ₁ i z = z^{w_i} χ₂ i z`, then the
  principal-series characters satisfy `χ₁(a) = (∏_i a_i^{w_i}) χ₂(a)`.
* `minorFun_borel_mul`: `v(a u g) = (∏_i a_i^{minorWeight c d i}) v(g)` for `a` diagonal and `u`
  upper unipotent, where `v = minorFun c d`.
* `mulFun_mem_principalSeries`, `mulFun_mem_kFiniteFunctions`: if
  `χ₁ i z = z^{minorWeight c d i} χ₂ i z`, then `g ↦ v(g) f(g)` lies in the principal series of
  `χ₁` (and is `U(n)`-finite) whenever `f` lies in that of `χ₂` (and is `U(n)`-finite).
* `mulV c d hχ : MKF n ds' →ₗ[ℂ] MKF n ds`: multiplication by `v`, with `mulV_coe`.
* `mulV_lie`: for `X` upper triangular,
  `mulV (π'(1 ⊗ X) h) = π(1 ⊗ X)(mulV h) − rightCharDeriv c d X • mulV h`, where `π'` and `π`
  are `complexStandardLie n ds'` and `complexStandardLie n ds`.
* `mulV_mem`: if `upperClosure (complexStandardLie n ds') T = ⊤` and `W ⊆ X(ds)` is
  `complexStandardLie n ds`-stable with `mulV T ∈ W`, then `mulV h ∈ W` for every `h ∈ X(ds')`.
* `eq_top_of_forall_mulV_mem`: a `U(n)`-stable subspace `W` of `X(ds)` with `mulV h ∈ W` for
  every `h ∈ X(ds')` is all of `X(ds)`.

## Proof

Write `v = minorFun c d`.

* `lie_mem_upperClosure`. Let `S'` be the set of `w ∈ upperClosure π v` with
  `π(1 ⊗ Y) w ∈ upperClosure π v` for every `Y`. It is a subspace. It contains `v`: write
  `Y = upperPart Y + skewPart Y` (Library `ComplexJacquetChart`). The skew part is
  skew-Hermitian and kills `v`, and the upper part is upper triangular. `S'` is stable under
  `π(1 ⊗ X)` for upper triangular `X`, because
  `π(1 ⊗ Y) π(1 ⊗ X) w = π(1 ⊗ X) π(1 ⊗ Y) w + π(1 ⊗ (YX − XY)) w`
  (`complex_map_commutator`). So `upperClosure π v ⊆ S'`. `lieAll_mem_upperClosure` follows by
  induction on tensors, since `z ⊗ Y = z • (1 ⊗ Y)`.
* `lie_skew_eq_zero`. For skew-Hermitian `Y`, `t ↦ exp(tY)` is a curve in `U(n)`
  (`skewExp`, Library `ComplexJacquetTorus`). The derivative clause of `IsComplexGKModule`
  gives that `t ↦ ℓ(ρ(exp tY) v)` has derivative `ℓ(π(1 ⊗ Y) v)` at `0` for every functional
  `ℓ`. The function is constant, so the derivative is `0`. Then
  `Module.forall_dual_apply_eq_zero_iff`.
* `rho_mem_upperClosure`. `upperClosure π v` is contained in its preimage under `ρ k`: that
  preimage contains `v = ρ k v`, and by the compatibility clause
  `ρ k π(1 ⊗ X) w = π(1 ⊗ k X k*) ρ k w` and `lie_mem_upperClosure` it is stable under the
  upper triangular directions.
* `upperClosure_eq_top`: apply cyclicity to `upperClosure π v`.
* `minorFun_borel_mul`, `mulFun_mem_principalSeries`. `a u` is upper triangular with diagonal
  `a`, so `minorMonomial_upper_mul` applies. Smoothness of the product is
  `ComplexJacquetLimit.contMDiff_mul_fun` with `contMDiff_minorFun`. The equivariance combines
  `minorFun_borel_mul`, the equivariance of `f` and `principalSeriesCharacter_eq_prod_mul`.
  `U(n)`-finiteness is `mul_mem_kFiniteVectors` with `minorFun_mem_kFiniteVectors`.
* `mulV_lie`. Both sides are right derivatives (`principalSeriesLie_one_tmul_apply_coe`). By
  the product rule `ComplexTemperedComplement.rightDerivative_mul_fun`,
  `R(X)(v h) = R(X)v · h + v · R(X)h`. For upper triangular `X`, `R(X) v = rightCharDeriv c d X · v`
  (`rightDerivative_minorFun`).
* `mulV_mem`. By `mulV_lie`, the preimage of `W` under `mulV` contains `T` and is stable under
  `π'(1 ⊗ X)` for upper triangular `X`. So it contains `upperClosure π' T = ⊤`.
* `eq_top_of_forall_mulV_mem` (Godement's argument). Suppose `W ≠ ⊤` and pick `f ∉ W`. The
  image `W'` of `W` in the functions on `GL_n(ℂ)` is `U(n)`-stable. The Library theorem
  `complexStandardAnnihilator` gives `u` in `X(ds.map complexCharacterDataInv)` and `k₀ ∈ U(n)`
  with `u(k₀) ≠ 0` and `∫_{U(n)} w u = 0` for every `w ∈ W'` (Haar probability measure
  `ComplexDuality.unitaryHaar`).
  - Let `k₁ = k₀⁻¹ · revUnitary n`, `u_t = R(k₁⁻¹) u` and `F = v · u_t`. By `hχ` and
    `complexPositionCharacter_map_inv_mul`, the characters satisfy
    `χ'_i(z)⁻¹ = z^{minorWeight c d i} · χ^{inv}_i(z)`. So `F` lies in the `U(n)`-finite principal
    series of `χ'⁻¹` (`mulFun_mem_kFiniteFunctions`).
  - Choose `s` with `|χ'_i(z)|² = |z|^{2 s_i}` (`exists_normSq_complexPositionCharacter`). The
    Gram-weighted conjugate `H = ComplexDuality.partner s F` then lies in `X(ds')`
    (`partner_mem_principalSeries`, `partner_mem_kFiniteVectors`). On `U(n)` the Gram weight is
    `1` (`gramWeight_unitary`), so `H(κ k₁) = conj(v(κ k₁) u(κ))` for `κ ∈ U(n)`.
  - `R(k₁)(mulV H) ∈ W` by hypothesis and `U(n)`-stability. Its pairing with `u` is
    `∫_{U(n)} |v(κ k₁) u(κ)|² dκ`, so this integral is `0`.
  - The integrand is continuous and nonnegative. At `κ = k₀` it equals
    `|v(revUnitary n) u(k₀)|² > 0` (`minorMonomial_revUnitary_ne_zero`, `u(k₀) ≠ 0`). So the
    integral is positive (`integral_unitaryHaar_pos`), a contradiction.
* `complexMinorProductCyclic`. Take `f₀ = mulV c d hχ T`; the formula for `f₀` holds by
  definition. Given `W` as in the conclusion, `upperClosure_eq_top` for the module `X(ds')`
  (`isComplexGKModule_complexStandardModule`) and `mulV_mem` give `mulV h ∈ W` for every `h`.
  Then `eq_top_of_forall_mulV_mem` gives `W = ⊤`.
