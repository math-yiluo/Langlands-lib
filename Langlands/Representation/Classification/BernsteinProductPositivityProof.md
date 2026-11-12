# Proof of positivity of binary products with unitary top shifted derivatives

Author: Worker 210.

The closing theorem
`Langlands.Classification.bernsteinUnitaryTopDerivativeProductPositivity F T`
proves exactly the published proposition
`Langlands.Classification.BernsteinUnitaryTopDerivativeProductPositivity.{uF, uV} F T`
from [BernsteinProductPositivityStatement](BernsteinProductPositivityStatement.md).
It holds for every prime `p`, every `F : PadicField.{uF} p`, every
`T : F.TopologicalData`, every unitary additive character `ψ` and independent
universes `uF` and `uV`. The statement pair and the pairs it imports are
unchanged. The proof uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

The route follows the provenance sketch in the statement Markdown (Bernstein,
LNM 1041, sections 7.3, 7.8 and 8.2). Every step is proved here on the actual
objects or taken from published Library results. The proof adds no hypotheses.
It covers ranks `a = 0` and `b = 0` and bounds `r = 0` and `s = 0`. It uses no
classification, temperedness or square-integrability result.

## Notation

For a smooth representation `X` of `GL_n(F)`, an exponent of `X` is an element
of `bernsteinCentralExponents T X`. Such an `e` comes with an actual irreducible
subquotient `D` of `X` and a scalar character `ω` of `D` along
`GeneralLinear.scalar`, with `‖ω a‖ = |a|^e` for all `a : F^×`. Here `|·|` is
`T.normalizedAbs`. Write `ν^s X` for `T.segmentFactor X s`, so the shifted
derivative is `ν^(1/2) X^(k)` (`bernsteinShiftedDerivative`).

## Proof of the closing theorem

Fix `A`, `B`, `r`, `s` and the hypotheses of the statement. Let `k ≤ a + b` with
`k < r + s`, and let `e` be an exponent of `ν^(1/2) (A × B)^(k)`.

1. Undoing the twist (`mem_bernsteinCentralExponents_of_segmentFactor`),
   `e - (a + b - k)/2` is an exponent of `(A × B)^(k)`. It is witnessed by an
   actual irreducible subquotient `D`.
2. The derivatives of `A` and `B` have finite length by
   `Derivative.generalLinearDerivativeFiniteLength`. Then the published
   `Derivative.BinaryDerivativeSupport.factorData` gives an order pair
   `(i, j)` in the Leibniz index set, so `i + j = k`, `i ≤ a` and `j ≤ b`. It
   also gives actual irreducible subquotients `E` of `A^(i)` and `H` of `B^(j)`,
   with `D` an actual subquotient of the rank cast of the binary normalized
   product `E × H`.
3. `exists_exponent_add_of_product` gives exponents `e₁` of `E` and `e₂` of `H`
   with `e - (a + b - k)/2 = e₁ + e₂`.
4. `derivative_exponent_bound`, applied to `A` and `E`, gives `i ≤ r` and
   `e₁ + (a - i)/2 ≥ 0`, with strict inequality when `i < r`. The same holds for
   `B`, `H`, `j` and `s`.
5. Since `(a - i) + (b - j) = a + b - k`, we get
   `e = (e₁ + (a - i)/2) + (e₂ + (b - j)/2)`. As `i + j = k < r + s`, either
   `i < r` or `j < s`. So one summand is positive and the other nonnegative,
   and `e > 0`.

## Declarations

All auxiliary declarations are in the namespace
`Langlands.Classification.BernsteinProductPositivity`.

| Declaration | Content |
| --- | --- |
| `hasScalarCharacter_of_isSubquotient` | A scalar character of a smooth representation is inherited by each of its actual subquotients. It passes to the subrepresentation and then to its quotient. |
| `scalarCharacter_eq` | On a nonzero carrier, two scalar characters along the same map agree. |
| `exponent_eq` | If `|a|^e = |a|^e'` for every `a : F^×`, then `e = e'`. Evaluate at the uniformizer, where `|ϖ| = q^(-1)` with `q > 1`, and take logarithms. |
| `exists_hasBernsteinCentralExponent` | Every irreducible smooth representation `D` of `GL_n(F)`, including `n = 0`, has an exponent. `GL_n(F)` is second countable, so `D` has countable dimension (`Whittaker.MirabolicRigidity.rank_le_aleph0`). Schur's lemma in that form (`exists_scalar_of_commute`) makes each central scalar act by a number `c a`. These numbers form a character `ω : F^× →* ℂ^×`. Smoothness makes its kernel open (`HasScalarCharacter.isOpen_ker`), and `T.norm_eq_normalizedAbs_rpow_of_isOpen_ker` writes `‖ω a‖` as a real power of `|a|`. |
| `hasBernsteinCentralExponent_segmentFactor` | If `D` on `GL_n` has exponent `e`, then `ν^s D` has exponent `e + n s`. It uses `T.hasScalarCharacter_segmentFactor` and `T.coe_determinantPowerCharacter_scalar`. |
| `mem_bernsteinCentralExponents_segmentFactor` | If `e` is an exponent of `X`, then `e + n s` is an exponent of `ν^s X`. Irreducibility and the subquotient relation both pass through the twist. |
| `segmentFactorNegIso` | The isomorphism `ν^(-s) (ν^s X) ≅ X`, from `twist_twist`, `realPowerCharacter_add` and `twist_one`. |
| `mem_bernsteinCentralExponents_of_segmentFactor` | If `e` is an exponent of `ν^s X`, then `e - n s` is an exponent of `X`. |
| `norm_scalarCharacter_eq_one` | Let `U` be finite-length and unitarizable, and `D` an actual irreducible subquotient of `U` with scalar character `ω`. Then `‖ω a‖ = 1`. Write `D` as a quotient of a subrepresentation `X ⊆ U`; `X` has finite length. `ScalarSubReduction.centralDefect_not_injective` gives a nonzero `x ∈ X` with `a · 1` acting by `ω a`. Its image `y ∈ U` is nonzero. Invariance of the positive form gives `|ω a|^2 ⟨y, y⟩ = ⟨y, y⟩`, and definiteness gives `|ω a| = 1`. |
| `exponent_eq_zero_of_isUnitarizable` | Every exponent of a finite-length unitarizable representation is `0`. |
| `reindex_scalar` | The entry-preserving reindex along `finCongr h` fixes scalar matrices. |
| `scalarCharacter_eq_one_of_rank_eq_zero` | On `GL_0`, the scalar character of a representation on a nonzero carrier is trivial. |
| `hasScalarCharacter_binaryProduct` | If nonzero `E` and `H` have scalar characters `ω₁` and `ω₂`, then the actual binary normalized product has scalar character `ω₁ ω₂`, in all ranks. If a rank is `0`, the product is the published rank-zero tensor functor: the rank-zero character is trivial and the scalar acts on the other tensor factor. In positive ranks, use `T.hasScalarCharacter_normalizedProductInduced` with `∏ i : Fin 2, c i = ω₁ ω₂`. |
| `hasScalarCharacter_rankCast` | `Derivative.generalLinearRankCast` keeps the scalar character. |
| `exists_exponent_add_of_product` | Let `E` and `H` be irreducible and `D` an irreducible subquotient of the rank cast of `E × H`. Then every exponent of `D` is `e₁ + e₂`, for exponents `e₁` of `E` and `e₂` of `H`. |
| `derivative_exponent_bound` | Let a factor `A` of rank `a` and bound `r ≤ a` satisfy the hypotheses of the statement. Let `e` be an exponent of `A^(i)`. Then `i ≤ r`, because higher derivatives are zero and a zero object has no irreducible subquotient. Also `e + (a - i)/2 ≥ 0`, with strict inequality when `i < r`. Strict positivity below `r` is the hypothesis after the `ν^(1/2)` shift. At `i = r` the shifted derivative has finite length (`finiteLength_twist_iff`) and is unitarizable, so its shifted exponent is `0`. |
| `Langlands.Classification.bernsteinUnitaryTopDerivativeProductPositivity` | The closing theorem described above. |
