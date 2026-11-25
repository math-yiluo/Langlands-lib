# Intertwiners to the reversed standard module of a Langlands-ordered character list

Lean module: `Langlands.Representation.Archimedean.RealCharacterReverseKernel`.

This module was written for the proof of
`RealStandardIrreducibleCriterionStatement`; the Library's proof of that statement (in
`RealLargeLanglandsQuotientInjectiveProof`) does not import this module. It proves the statement
`RealReverseIntertwinerKernelStatement` (Rev, Library module
`RealStandardIrreducibleCriterionReduction`) for lists of character blocks, ties allowed. The
proof is conditional on three statements stated in the Library (see "The statement"). The
statement is `Langlands.Archimedean.RealCharacterReverseKernelStatement`, proved as
`Langlands.Archimedean.realCharacterReverseKernel`. Lists with induced `GL_2` blocks are not
covered.

Notation: `GL_n(ℝ)` is `Langlands.GeneralLinear n ℝ`, `O(n)` is `unitaryCompact ℝ n` with the
Haar probability measure `dκ = RealPrincipalSeriesDuality.haarK n`. `R(k)` is
`Whittaker.rightTranslation ℂ _ k` (`R(k) f (x) = f(x k)`). A `RealBlock` is `.character d`
(the character `sgn^ε |·|^t` of `ℝˣ`, rank `1`) or `.induced d` (rank `2`); `realRank ds` is the
total rank, and `realBlockExponent x` the real part of the exponent of `x`
(`RealGenericParameterReduction`). `IsRealLanglandsOrdered ds` says that `realBlockExponent` is
non-increasing along `ds`. `RealStrictCharacterLanglandsQuotient.IsCharacterList ds` says that
every block of `ds` is a character block. For a list `ds`,
`I(ds) = kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)` is the space of
`O(n)`-finite functions of the standard module. `realPositionCharacter ds` and
`realPositionExponent ds` are the characters and exponents at the positions. `dualChar χ` is the
family `l, x ↦ (χ_l x)⁻¹`. `principalSeries ℝ n χ` is the Library's smooth principal series.
`IsRealStandardIntertwiner` (`RealGenericParameterReduction`) and `IsGKSubmodule` are the Library
definitions: compatibility with right translation by `O(n)` and with all right derivatives.

Unprefixed declarations below are in the namespace
`Langlands.Archimedean.RealCharacterReverseKernel`, except the statement and the main theorem,
which are in `Langlands.Archimedean`.

## The statement

`RealCharacterReverseKernelStatement` assumes three statements stated in the Library:

* `RealBlockChartIntegrableStatement` (proved as `realBlockChartIntegrable`);
* `RealBlockParabolicIntegrationStatement` (proved as `realBlockParabolicIntegration`);
* `RealTemperedStandardIrreducibleStatement` (proved as `realTemperedStandardIrreducible`).

Under these assumptions it says the following. Let `n : ℕ` and `ds : List RealBlock`, let
`T : I(ds) →ₗ[ℂ] I(ds.reverse)` be `ℂ`-linear, and let `W` be a `ℂ`-submodule of `I(ds)`. Assume:

* `realRank ds = n`;
* `IsCharacterList ds`, that is, `∀ b ∈ ds, ∃ c, b = .character c`;
* `IsRealLanglandsOrdered ds`;
* `T` is an intertwiner:
  `IsRealStandardIntertwiner n (realStandardRep n ds.reverse) (realStandardLie n ds.reverse) ds T`;
* `W` is a `(𝔤, K)`-submodule: `IsGKSubmodule (realStandardRep n ds) (realStandardLie n ds) W`;
* `W ≠ ⊤`.

Then `W ≤ LinearMap.ker T`.

The conclusion is the one of `RealReverseIntertwinerKernelStatement`, word for word, for the
same hypotheses plus `IsCharacterList ds`.

Provenance. Derived from the Library statement `RealReverseIntertwinerKernelStatement` by
restricting it to lists of character blocks and making it conditional on the three statements
above; no additional literature statement is claimed. The source of Rev, as recorded in
`RealStandardIrreducibleCriterionReduction.md`, is Langlands' theorem in the form of Mœglin's
Theorem 4 (C. Mœglin, Representations of GL(n) over the real field, Proc. Sympos. Pure Math. 61
(1997), printed p. 159; `bailey-knapp-1997-pspm61`, PDF page = printed page + 9): for a positive
character `χ` of the diagonal torus, `I(w₀χ)` has a unique irreducible submodule, isomorphic to the
Langlands quotient `J(χ)` of `I(χ)`, and `J(χ)` occurs with multiplicity one in `I(χ)`. See also
Knapp 1986, Theorem 8.54 (printed p. 267) and Proposition 8.61 (printed p. 274) (Library source
`provided-40cace9c0f8c2361e7b3d7459f7908362f819b68114945405f1c16d968b21855`, PDF page = printed
page + 14). For a character list, `I(ds)` is the principal series of the position characters and
`I(ds.reverse)` that of the reversed characters. The proof below does not use Langlands'
theorem. It is internal: it combines the block Jacquet functional of `RealBlockFunctional` with the
transposition and twist device of the complex reversal argument (modules `ComplexReverseTransfer`
and `ComplexReverseTwist`).

## Auxiliary results

* `realRank_eq_length`: for a character list, `realRank ds = ds.length`.
* `realPositionCharacter_inv`: for a character list,
  `realPositionCharacter ds l z⁻¹ = (realPositionCharacter ds l z)⁻¹`.
* `realPositionCharacter_append`: for a character list `A`, the position character of `A ++ B` at
  `l` is that of `A` at `l` if `l < A.length`, and that of `B` at `l − A.length` otherwise.
* `realPositionCharacter_reverse`: for a character list and `l < ds.length`,
  `realPositionCharacter ds.reverse l = realPositionCharacter ds (ds.length − 1 − l)`.
* `exists_testVector` (assumes the three statements). Let `realRank ds = n`, `IsCharacterList ds`
  and `IsRealLanglandsOrdered ds`, and write `χ = realPositionCharacter ds`. There is an
  `O(n)`-finite function `f` of `principalSeries ℝ n χ` with the following property. Let `U`, `X`
  be spaces of `O(n)`-finite functions of `principalSeries ℝ n (dualChar χ)`, both stable under
  `R(κ)` for `κ ∈ O(n)` and under all right derivatives, with `U ≠ ⊥`. Suppose that for every
  `x ∈ X` the function `g ↦ coeff x f (gᵀ)` lies in `nullCoeff χ U` (module
  `RealReverseRecursion`: `coeff x y g = ∫ x(κ g) y(κ) dκ`; `nullCoeff χ U` is spanned by the
  `coeff x y` with `y ⊥ U`). Then `x(1) = 0` for every `x ∈ X`.

Proofs.

* The four list lemmas are inductions on the list. The reversal lemma uses
  `List.reverse_cons` and the append lemma.
* `exists_testVector`. `χ` is a signed power with exponents `e = realPositionExponent ds`
  (`RealStrictCharacterLanglandsQuotient.isSignedPower`), with signs `p` from `exists_signs`.
  `exists_blocks` and `exponent_ord` (`RealCharacterLanglandsQuotient`) give a block
  decomposition `ks` with `dim ks = n` and `BlockOrdered ks e`. `exists_jac_testVector_ne_zero`
  (`RealBlockNonvanishing`, using `RealBlockChartIntegrableStatement`) gives a test vector `f`,
  with `jac ks e p f ≠ 0`, which is `O(n)`-finite in the principal series (`testVector_mem`). For
  `U`, `X` as above, `RealReverseRecursion.jac_eq_zero_of_transpose` gives
  `x(1) · jac ks e p f = 0`; it uses both block statements and `TiedIrreducible`, supplied by
  `realTiedIrreducible` from `RealTemperedStandardIrreducibleStatement`. Hence `x(1) = 0`.

## Proof of the main theorem

`realCharacterReverseKernel`. Fix the three statements, `n`, `ds`, `T`, `W` with the hypotheses.
Let `χ = realPositionCharacter ds` and `ψ = realPositionCharacter ds.reverse`, signed powers. Write
`twist g = w₀ (gᵀ)⁻¹` and `twistLin n f = f ∘ twist` (module `RealReverseTwist`).

1. **Characters.** `ds.length = n` (`realRank_eq_length`). By the list lemmas,
   `ψ_{rev j} = χ_j` for `j < n`, and so `(dualChar ψ)_j(z) = χ_{rev j}(z⁻¹)` and
   `(dualChar χ)_j(z) = ψ_{rev j}(z⁻¹)`. These are the hypotheses of
   `RealReverseTwist.twistLin_mem_kFiniteFunctions`. So `twistLin n` maps the `O(n)`-finite
   functions of `principalSeries ℝ n χ` into those of `principalSeries ℝ n (dualChar ψ)`, and
   those of `principalSeries ℝ n ψ` into those of `principalSeries ℝ n (dualChar χ)`.
2. **The test vector.** Take `f` from `exists_testVector`.
3. **`W` as functions, and its annihilator.** Let `W'` be the image of `W` in the functions on
   `GL_n(ℝ)`. It lies in the `O(n)`-finite functions of `principalSeries ℝ n χ` and is stable
   under `R(k)`, `k ∈ O(n)`, and under right derivatives (from `IsGKSubmodule`,
   `realStandardRep_apply_coe`, `realStandardLie_one_tmul_apply_coe`). Since `W ≠ ⊤`, some
   `g ∈ I(ds)` is not in `W'`. Let `U = JacquetKernel.annihilator χ W'`, the `O(n)`-finite
   functions `u` of `principalSeries ℝ n (dualChar χ)` with `∫ u w = 0` over `O(n)` for all
   `w ∈ W'`. It is stable under `R(k)` and right derivatives (`annihilator_rightTranslation`,
   `annihilator_rightDerivative`), and `U ≠ ⊥` (`annihilator_ne_bot`, because `g ∉ W'`).
4. **The twisted image.** Let `X = twistLin n (T(W))`, as functions. By step 1 it lies in the
   `O(n)`-finite functions of `principalSeries ℝ n (dualChar χ)`. It is stable under `R(k)`,
   because `R(k)` commutes with `twistLin n` for `k ∈ O(n)` (`rightTranslation_twistLin`) and
   with `T`. It is stable under right derivatives, because
   `rightDerivative Y (twistLin n F) = twistLin n (rightDerivative (−Yᵀ) F)`
   (`rightDerivative_twistLin`) and `T` commutes with right derivatives.
5. **The pairing transpose.** `v = twistLin n f` is `O(n)`-finite in
   `principalSeries ℝ n (dualChar ψ)` (step 1). `RealReverseTransfer.exists_pairing_transpose`
   gives an `O(n)`-finite `u` of `principalSeries ℝ n (dualChar χ)` with `∫ u h = ∫ v (T h)` over
   `O(n)` for all `h ∈ I(ds)`.
6. **The coefficient identity.** For `w ∈ W` and `g ∈ GL_n(ℝ)`, with `x = twistLin n (T w)`,
   `coeff x f (gᵀ) = ∫ (T w)(twist(κ gᵀ)) f(κ) dκ`. This equals
   * `∫ (T w)(κ g⁻¹) f(twist κ) dκ` (`RealReverseTwist.integral_mul_inv_eq_twist`, with
     `twist ∘ twist = id`),
   * `= ∫ w(κ g⁻¹) u(κ) dκ` (`RealReverseTransfer.integral_mul_transfer` at `g⁻¹`, since
     `f ∘ twist = v`),
   * `= ∫ u(κ g) w(κ) dκ = coeff u w g` (`RealReverseTransfer.integral_mul_inv_swap`).

   Here `u` is `O(n)`-finite in `principalSeries ℝ n (dualChar χ)`, `w` is `O(n)`-finite in
   `principalSeries ℝ n χ`, and `∫ u' w = 0` for every `u' ∈ U` by definition of the
   annihilator. So `coeff u w` is a generator of `nullCoeff χ U`. Hence `g ↦ coeff x f (gᵀ)` lies in `nullCoeff χ U` for every
   `x ∈ X`.
7. **Vanishing at `1`.** By the property of `f` (step 2) applied to `U` and `X`, every `x ∈ X`
   vanishes at `1`.
8. **Conclusion.** Let `w ∈ W`. For `κ ∈ O(n)`, the element `w₀ κ` lies in `O(n)` (`w0GL_mem`),
   so `R(w₀ κ) w ∈ W` and `x = twistLin n (T (R(w₀ κ) w)) ∈ X`. Then
   `0 = x(1) = (T (R(w₀ κ) w))(twist 1) = (T w)(w₀ w₀ κ) = (T w)(κ)`, using `twist 1 = w₀`,
   `T R(k) = R(k) T` and `w₀² = 1`. So `T w` vanishes on `O(n)`. Being in a principal series, it is
   zero (`eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact`). Hence `W ≤ ker T`.

Axioms of `realCharacterReverseKernel`: `propext`, `Classical.choice`, `Quot.sound`.

## Dependencies

The proof uses the following modules:

* the modules of the block Langlands-quotient argument: `RealBlockChartBound`, `RealBlockLimit`, `RealBlockDual`,
  `RealBlockJacquet`, `RealBlockFunctional`, `RealBlockNonvanishing`, `RealTiedIrreducible` and
  `RealCharacterLanglandsQuotient` (`exists_signs`, `exists_blocks`, `exponent_ord`);
* the modules of the reversal argument: `RealBlockLimitValue`, `RealBlockSliceDecomposition`,
  `RealReverseTwist`, `RealReverseRecursion` and `RealReverseTransfer`.

From the rest of the Library it uses `JacquetKernel` (the annihilator),
`RealStrictCharacterLanglandsQuotient` (`isSignedPower`, `IsCharacterList`) and
`RealLargeLanglandsQuotientReduction` (`IsRealStandardIntertwiner.map_realStandardRep`,
`map_realStandardLie`).
