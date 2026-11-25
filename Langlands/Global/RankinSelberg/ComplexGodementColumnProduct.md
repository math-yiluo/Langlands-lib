# Fourier transforms of column-product tests (Jacquet 2009, (8.3)–(8.4))

Module `Langlands.Global.RankinSelberg.ComplexGodementColumnProduct`, namespace
`Langlands.Global.RankinSelbergGlobal.ComplexGodementColumnProduct`.

## Statement

In §8.3 of H. Jacquet, *Archimedean Rankin-Selberg integrals* (Contemp. Math. 489, 2009;
author-posted version, sha256 `7a11766e…afe`, pp. 58–59), the test function on
`(n-1) × n` matrices is taken to be a product `Φ(Y, X) = Φ₁(Y) Φ₂(X)`. Here `Y` is the square
`(n-1) × (n-1)` block and `X` the column of size `n-1`. To pass from (8.3) to the symmetric
integral (8.4), Jacquet replaces `Φ₁` by `F_ψ(Φ₁)` and `Φ₂` by `F_ψ(Φ₂)`. This uses the fact
that the Fourier transform of a product test is the product of the Fourier transforms of its
factors. Jacquet's Fourier transform (p. 3) is `F_ψ(Φ)(X) = ∫ Φ(Y) ψ(-Tr(ᵗX Y)) dY` for the
self-dual measure. `ComplexColumnProductFourierStatement` is this factorization at a complex
place, with `m = n - 1`.

The data, all in the module:

- `lastColumn X : Fin m → ℂ` is the last column `i ↦ X i (Fin.last m)` of
  `X : Matrix (Fin m) (Fin (m + 1)) ℂ`.
- `leadingColumns X : Matrix (Fin m) (Fin m) ℂ` is `X.submatrix id Fin.castSucc`, the first `m`
  columns.
- `columnProduct Φ φ` is, for `Φ : 𝓢(Matrix (Fin m) (Fin m) ℂ, ℂ)` and `φ : 𝓢(Fin m → ℂ, ℂ)`,
  the Schwartz function on `m × (m+1)` matrices with value `Φ (leadingColumns X) * φ (lastColumn X)`
  (`columnProduct_apply`). Matrix spaces carry the operator norm (`Matrix.Norms.Operator`).
- The measure on matrices is the Library's `rectangularMeasure (complexSelfDualMeasure a)`, the
  product over all entries of the self-dual measure for `ψ_a = complexScaledCharacter a`.
- The Library's `rectangularFourierIntegral ψ μ f Z = ∫ Y, f Y * ψ.complex (Σ_(i,j) Y_ij Z_ij)`
  has a plus sign. Evaluated at `-X`, it is Jacquet's `F_ψ(f)(X)` (the pairing is
  `Tr(ᵗX Y)`).
- `vectorFourierIntegral a f w = ∫ v, f v * ψ_a(-Σ_i v_i w_i)` against
  `Measure.pi (fun _ => (complexSelfDualMeasure a).measure)`. It is Jacquet's `F_ψ` on columns.

The statement: for all `m`, `a ∈ ℂˣ`, `Φ`, `φ` and `X`,

`rectangularFourierIntegral ψ_a μ_a (columnProduct Φ φ) (-X) =
  rectangularFourierIntegral ψ_a μ_a Φ (-leadingColumns X) * vectorFourierIntegral a φ (lastColumn X)`,

that is, `F_ψ(Φ ⊗ φ)(X) = F_ψ(Φ)(leadingColumns X) · F_ψ(φ)(lastColumn X)`. The module proves it
in `complexColumnProductFourier`, with no premise.

It also proves:

- `rectangularFourierIntegral_column_mul`: the same factorization for arbitrary functions
  `f₁ : Matrix (Fin m) (Fin m) ℂ → ℂ` and `f₂ : (Fin m → ℂ) → ℂ`, any unitary character `ψ` of
  `ℂ` and any σ-finite additive Haar measure `μ`, with plus signs at an arbitrary `Z`. It needs
  no integrability hypothesis.
- `lastColumnFourierIntegral_columnProduct`: the partial Fourier integral in the last column,
  `lastColumnFourierIntegral a F X = vectorFourierIntegral a (v ↦ F (columnJoin (leadingColumns X) v)) (lastColumn X)`,
  sends `columnProduct Φ φ` to `X ↦ Φ (leadingColumns X) * vectorFourierIntegral a φ (lastColumn X)`.
  Here `columnJoin S v` is the matrix with leading columns `S` and last column `v`.

## Provenance

The statement is internal. It serves the passage from (8.3) to (8.4) in Jacquet's proof, with
the split at the last column, which matches the Library's Godement section conventions. Jacquet uses the factorization without stating it as a
lemma. The only changes from Jacquet are the explicit character `ψ_a` with its self-dual
measure, the Library's plus-sign rectangular integral evaluated at `-X`, and `m = n - 1 ≥ 0`
rows.

## Proof

**Schwartz product.** `schwartzProd L₁ L₂ hC0 hC f₁ f₂` is the Schwartz function
`x ↦ f₁ (L₁ x) * f₂ (L₂ x)`, for continuous real-linear maps `L₁`, `L₂` with
`‖x‖ ≤ C (‖L₁ x‖ + ‖L₂ x‖)` and `0 ≤ C`. Smoothness is that of a product of compositions. For
decay, Mathlib's Leibniz bound `norm_iteratedFDeriv_mul_le` bounds the `n`-th derivative of
the product. `norm_iteratedFDeriv_comp_le` bounds the `i`-th derivative of `f ∘ L` by
`‖D^i f (L x)‖ ‖L‖^i`. The weight satisfies
`‖x‖^k ≤ C^k (1 + ‖L₁ x‖)^k (1 + ‖L₂ x‖)^k`. Each weighted factor
`(1 + ‖y‖)^k ‖D^i f y‖` with `i ≤ n` is bounded by a Schwartz seminorm
(`SchwartzMap.one_add_le_sup_seminorm_apply`, packaged in `exists_one_add_pow_mul_le`).

**Column product.** `leadingColumnsCLM` and `lastColumnCLM` are the two maps as continuous
real-linear maps. `leadingJoinCLM S = columnJoin S 0` and `lastJoinCLM v = columnJoin 0 v` satisfy
`leadingJoinCLM (leadingColumns X) + lastJoinCLM (lastColumn X) = X`. This gives
`norm_le_columnJoin`, the norm bound with `C = ‖leadingJoinCLM‖ + ‖lastJoinCLM‖`.
`columnProduct` is `schwartzProd` for these data.

**Measure-preserving split.** `columnSplitEquiv m` is the measurable equivalence
`X ↦ (lastColumn X, leadingColumns X)` (`columnSplitEquiv_apply`, using
`Fin.succAbove_last`). It applies Mathlib's `piFinSuccAbove` at `Fin.last m` in each row and then
`arrowProdEquivProdArrow`. `measurePreserving_columnSplitEquiv` shows that it carries the
nested product measure of `ν` on `m × (m+1)` matrices to the product of the vector measure and
the nested product measure on `m × m` matrices, for every σ-finite `ν`. The proof combines
`measurePreserving_pi`, `measurePreserving_piFinSuccAbove` and
`measurePreserving_arrowProdEquivProdArrow`.

**Factorization.** `rectangularPairing_eq_add` splits the pairing by `Fin.sum_univ_castSucc`:
`⟨Y, Z⟩ = Σ_i Y_(i,m) Z_(i,m) + ⟨leadingColumns Y, leadingColumns Z⟩`. Since `ψ.complex` is an
additive character (`AddChar.map_add_eq_mul`), the integrand of the rectangular Fourier integral
is `g (columnSplitEquiv m Y)`, with `g (v, S) = (f₂ v ψ(Σ v_i Z_(i,m))) (f₁ S ψ(⟨S, leadingColumns Z⟩))`.
`MeasurePreserving.integral_comp'` moves the integral to the product measure, and Mathlib's
`integral_prod_mul` factors it. That lemma holds without integrability, since both sides are
zero in the non-integrable cases. This proves `rectangularFourierIntegral_column_mul`.
`complexColumnProductFourier` specializes it to `ψ_a`, `μ_a`, `f₁ = Φ`, `f₂ = φ` and `Z = -X`,
using `leadingColumns (-X) = -leadingColumns X`, `lastColumn (-X) = -lastColumn X` and
`Σ v_i (-w_i) = -Σ v_i w_i`.

**Partial transform.** `lastColumnFourierIntegral_columnProduct` follows from
`leadingColumns (columnJoin S v) = S`, `lastColumn (columnJoin S v) = v` and
`integral_const_mul`.

The module sets `backward.isDefEq.respectTransparency false`, as other Library modules that use
operator norms of continuous linear maps between matrix spaces do.
