# Intertwiners to the reversed standard module: the Langlands-ordered case

Lean module: `Langlands.Representation.Archimedean.ComplexReverseIntertwinerTied`. Worker 5677
wrote it under Task 7064 (`e4a22cc7-0a28-44a3-afc6-38bb7c243851`).

## Notation

`GL_n(ℂ)` is `Langlands.GeneralLinear n ℂ`, `U(n)` is `unitaryCompact ℂ n` with Haar probability
measure `ComplexDuality.unitaryHaar n`. For a list `ds` of `ComplexCharacterData`, `I(ds)` is the
`(𝔤𝔩_n(ℂ), U(n))`-module `(complexStandardRep n ds, complexStandardLie n ds)` on
`kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)`: the `U(n)`-finite functions
of the smooth principal series of the characters `χ_j = complexPositionCharacter ds j`. An
intertwiner `T : I(ds) → I(es)` is a `ℂ`-linear map with
`IsComplexStandardIntertwining n (complexStandardRep n es) (complexStandardLie n es) ds T`.
`IsComplexLanglandsOrdered ds` says that the real parts of the exponents of `ds` are
non-increasing along the list. The twist `σ(g) = w₀ (gᵀ)⁻¹` is `ComplexReverseTwist.twist`, and
`twistLin n f = f ∘ σ`.

## The statement

`Langlands.Archimedean.ComplexReverseIntertwinerKernelReductionStatement`:

`ComplexTemperedStandardIrreducibleStatement → ComplexReverseIntertwinerKernelStatement`.

The hypothesis `ComplexTemperedStandardIrreducibleStatement` (module
`ComplexTemperedIrreducibleStatement`) says: if all exponents of `ds` have the same real part, then
`I(ds)` is irreducible. It is not yet proved in the Library.

The proof also uses two block statements. The Library proves both: `complexBlockChartIntegrable`
(module `ComplexBlockChartIntegralProof`) and `complexBlockParabolicIntegration` (module
`ComplexBlockParabolicIntegrationProof`). The theorem
`le_ker_of_isLanglandsOrdered` keeps them as explicit hypotheses, and the final reduction supplies
them. The three statements used by the proof are:

- `ComplexBlockChartIntegrableStatement` (module `ComplexBlockChartIntegralStatement`):
  integrability on `M_{k×a}(ℂ)` of the block chart bound
  `∏_{l<a} det(1 + X_{≤l}ᴴ X_{≤l})^{ε_l} · ∏_{1 ≤ j < k} det(1 + X^{(j)} X^{(j)ᴴ})^{-1}` when
  `∑_{l ≥ j} (ε_l + 1) < 0` for all `j < a`.
- `ComplexBlockParabolicIntegrationStatement`: the integration formula
  `∫_{U(a+k)} F = c ∫_{U(a)} ∫_{U(k)} ∫_{M_{k×a}(ℂ)} F(n̄(X) diag(κ₁, κ₂)) dX dκ₂ dκ₁` for `F` in the
  principal series of the modulus character, with integrability of the inner integrand.
- `ComplexTemperedStandardIrreducibleStatement`, as above.

The conclusion `ComplexReverseIntertwinerKernelStatement` (Rev_C) was stated by Worker 728 in the
module `ComplexStandardIrreducibleCriterionReduction` (published from candidate
`f94dfe9f-7bf7-40a4-8de6-05842c2a02b4`). It says: for every `n`, every list `ds` of `n` complex
characters with `IsComplexLanglandsOrdered ds`, every intertwiner `T : I(ds) → I(ds.reverse)` and
every `(𝔤, K)`-submodule `W` of `I(ds)` (`IsGKSubmodule`) with `W ≠ ⊤`, `W ≤ ker T`.

The statement is proved by `Langlands.Archimedean.complexReverseIntertwinerKernelReduction`.
It applies `ComplexReverseIntertwinerTied.le_ker_of_isLanglandsOrdered` to
`complexBlockChartIntegrable`, `complexBlockParabolicIntegration` and the tempered hypothesis.

### Provenance

Derived (internal). This is a reduction: it proves Rev_C from the Library statement
`ComplexTemperedStandardIrreducibleStatement` and adds no other hypothesis. The Markdown of
`ComplexStandardIrreducibleCriterionReduction` explains why Rev_C holds in Langlands' classification: the image of a nonzero intertwiner
`I(ds) → I(ds.reverse)` is the Langlands quotient, so its kernel is the largest proper submodule.
The formal proof does not follow that route. It extends the proof of the strictly ordered case
(`ComplexStrictReverseIntertwinerKernelStatement`, module `ComplexReverseIntertwinerStrict`) to
blocks of tied exponents, using the block Jacquet functional of Worker 140 (Task 7063).

## Supporting modules

- Worker 5677 (Task 7064): `ComplexReverseTwist` (the twist `σ`, `twistLin`, pullback of principal
  series), `ComplexReverseTransfer` (pairing transpose and transfer identity),
  `ComplexReverseRecursion` (`integral_mul_swap`), `ComplexReverseIntertwinerStrict`
  (`complexPositionCharacter_inv`, `complexPositionCharacter_reverse`) and
  `ComplexReverseBlockRecursion` (the recursion `mul_jac_eq_zero` along the blocks).
- Worker 140 (Task 7063): `ComplexBlockFunctional` (block decompositions, `BlockOrdered`, the block
  Jacquet functional `jac`, `TiedIrreducible`), `ComplexBlockDual`, `ComplexBlockNonvanishing`
  (`exists_jac_testVector_ne_zero`: a `U(n)`-finite test vector with nonzero `jac`) and
  `ComplexBlockLanglandsQuotient` (`exists_blockOrdered`, `exponent_ordered`, and `tiedIrreducible`:
  `ComplexTemperedStandardIrreducibleStatement → TiedIrreducible`).
- Worker 728 (Task 7064): `ComplexBlockLimitSum` and `ComplexBlockSlice`, used by
  `ComplexReverseBlockRecursion`.
- Library: `ComplexJacquetKernel` (the annihilator of a proper stable space and its stability),
  `ComplexStrictLanglandsQuotient.isPhasePower`, and the block proofs `complexBlockChartIntegrable`
  and `complexBlockParabolicIntegration`.

## Results of this module

- `rightDerivative_twistLin`: for smooth `f` and `X ∈ M_n(ℂ)`,
  `rightDerivative X (f ∘ σ) (g) = rightDerivative (-Xᵀ) f (σ g)`.
- `le_ker_of_isLanglandsOrdered hT1 hT3 hU n ds T W hn hord hT hW hW' : W ≤ LinearMap.ker T`,
  with the three statements as hypotheses and the hypotheses of Rev_C.

## Proof of `rightDerivative_twistLin`

`(f ∘ σ)(g h) = F(A (h⁻¹)ᵀ)` with `A = σ(g)` and `F` the extension of `f` to an open set of
matrices (`unitsExtension`), because `σ(g h) = σ(g) (h⁻¹)ᵀ`. The derivative of
`y ↦ A (y⁻¹)ᵀ` at `1` is `X ↦ A (-X)ᵀ` (`hasFDerivAt_ringInverse`, transposition is linear). By
the chain rule and `mfderiv_eq_fderiv_of_eq_comp`, `rightDerivative X (f ∘ σ) (g)` is the derivative
of `F` at `A` in the direction `A (-Xᵀ)`, which is `rightDerivative (-Xᵀ) f (A)`
(`rightDerivative_eq_fderiv`).

## Proof of `le_ker_of_isLanglandsOrdered`

Let `χ` and `ψ` be the position characters of `ds` and `ds.reverse`, and `e` the exponents of
`χ`. Both are phase-power characters (`isPhasePower`). The real parts of `e` are non-increasing
(`exponent_ordered`), so `exists_blockOrdered` cuts `0, …, n-1` into blocks `ks` with
`BlockOrdered ks e` and `n = dim ks`. As in the strict case, `ψ⁻¹_j(z) = χ_{n-1-j}(z⁻¹)` and
`χ⁻¹_j(z) = ψ_{n-1-j}(z⁻¹)`.

1. The annihilator. View `W` as a space of functions on `GL_n(ℂ)`. It is stable under right
   translation by `U(n)` and under right derivatives, and some vector of `I(ds)` is not in `W`.
   The annihilator of `W` in the `U(n)`-finite principal series of `χ⁻¹`
   (`ComplexJacquetKernel.annihilator`) is stable and nonzero (`annihilator_rightTranslation`,
   `annihilator_rightDerivative`, `annihilator_ne_bot`). So every `w ∈ W` satisfies
   `IsOrthStable n χ w`.
2. A test vector. `exists_jac_testVector_ne_zero` gives a `U(n)`-finite `f₀` in the principal
   series of `χ` with `jac ks e p f₀ ≠ 0` (`p` the weights of `ds`). Put `v = f₀ ∘ σ`, which lies
   in the `U(n)`-finite principal series of `ψ⁻¹` (`twistLin_mem_kFiniteFunctions`), and let `u`
   be its pairing transpose (`exists_pairing_transpose`): `⟨u, h⟩ = ⟨v, T h⟩` for `h ∈ I(ds)`.
3. A transposed identity. For `w ∈ W` and `g ∈ GL_n(ℂ)`,
   `∫ u(κ g) w(κ) dκ = ∫ (T w ∘ σ)(κ gᵀ) f₀(κ) dκ`. This is the chain `integral_mul_swap`,
   `integral_mul_transfer` (both at `g⁻¹`) and the change of variables
   `integral_mul_inv_eq_twist`, together with `σ ∘ σ = id`.
4. The twisted image. Let `U = {T w ∘ σ : w ∈ W}`. It consists of `U(n)`-finite functions of the
   principal series of `χ⁻¹`. It is stable under right translation by `U(n)`: by
   `rightTranslation_twistLin`, a translate of `T w ∘ σ` is `T w' ∘ σ` with `w'` a translate of
   `w` by a conjugated unitary matrix, and `T` commutes with `U(n)`. It is stable under right
   derivatives: by `rightDerivative_twistLin`, `R(X)(T w ∘ σ) = (R(-Xᵀ) T w) ∘ σ = T(R(-Xᵀ) w) ∘ σ`.
5. Recursion. By step 3 at `gᵀ`, each `x = T w ∘ σ ∈ U` satisfies
   `M_{x,f₀}(g) = M_{u,w}(gᵀ)` with `w` orthogonal to a nonzero stable space (step 1), so
   `HasTransposeExpansion n χ x f₀` holds with one term. `TiedIrreducible` follows from
   `ComplexTemperedStandardIrreducibleStatement` (`tiedIrreducible`).
   `ComplexReverseBlockRecursion.mul_jac_eq_zero` gives `x(1) · jac ks e p f₀ = 0` for `x ∈ U`.
   Since `σ(1) = w₀` and `jac ks e p f₀ ≠ 0`, `(T w)(w₀) = 0` for every `w ∈ W`.
6. Conclusion. For `w ∈ W` and `k ∈ U(n)`, `w₀ k ∈ U(n)` and the translate `R(w₀ k) w` lies in
   `W`, so `T(R(w₀ k) w)(w₀) = (T w)(w₀ w₀ k) = (T w)(k) = 0`. A function in the principal series
   that vanishes on `U(n)` is zero (`ComplexDuality.eq_zero_of_mem_principalSeries_of_eqOn`), so
   `T w = 0`.
