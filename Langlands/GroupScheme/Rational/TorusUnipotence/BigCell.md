# Graded big-cell injectivity

Module `Langlands.GroupScheme.Rational.TorusUnipotence.BigCell`, namespace
`Langlands.GroupScheme.TorusUnipotence`.

This module proves `GradedBigCellInjectivityStatement` from `BigCellStatement` as
`gradedBigCellInjectivity`. Let `A` be a formally smooth Noetherian domain over a field `k`, with a
`ℤ`-grading `𝒜`, an augmentation `ε` vanishing in nonzero degrees and an algebra map `Δ`
satisfying both counit laws. Assume the degree-zero part of `I = ker ε` lies in `I²`. Then
`bigCellMap 𝒜 ε Δ : A → A ⧸ minusIdeal ⊗ A ⧸ plusIdeal` is injective.

## Auxiliary declarations

*Variable substitutions.* For `σ` and a decidable predicate `P` on `σ`:

* `keepVars P : MvPolynomial σ k →ₐ[k] MvPolynomial σ k` sends `X s` to `X s` if `P s` holds and
  to `0` otherwise (`keepVars_X`).
* `keepVars_eq_zero`: if every monomial of `p` contains a variable outside `P`, then
  `keepVars P p = 0`.
* `keepVars_mem_idealOfVars`, `keepVars_pow_le_comap`: `keepVars P` preserves `idealOfVars` and
  its powers.
* `truncKeep P N`: the induced map on `T_N = MvPolynomial σ k ⧸ (idealOfVars) ^ N`.
  `truncKeep_mk` computes it on classes (`rfl`), and `truncKeep_mem` says it preserves
  `truncVarIdeal`.

*Weights.* For `w : σ → ℤ`:

* `exists_not_pos_of_weight_nonpos`, `exists_not_neg_of_weight_nonneg`: a nonzero exponent vector
  of weight `≤ 0` (resp. `≥ 0`) involves a variable of weight `≤ 0` (resp. `≥ 0`).
* `ne_zero_of_mem_support_of_constantCoeff`: a polynomial without constant term has no zero
  exponent vector in its support.
* `keepVars_pos_eq_zero`: keeping only the variables of positive weight kills every
  weighted-homogeneous polynomial of degree `≤ 0` without constant term.
  `keepVars_neg_eq_zero` is the mirror statement: keeping only the variables of negative weight
  kills those of degree `≥ 0`.

*Tensor products.* `productMap_sub_mem_sq ε J f g hf hg t`. Let `f, g : A →ₐ[k] B` agree with `ε`
modulo an ideal `J`. Then for every `t ∈ A ⊗ A`,
`productMap f g t - f (rid ((id ⊗ ε) t)) - g (lid ((ε ⊗ id) t)) + ε (rid ((id ⊗ ε) t)) ∈ J²`.

## Main statements

* `mem_pow_of_bigCellMap_eq_zero`. Let `A` be formally smooth, let `ε` vanish in nonzero degrees,
  and let `Δ` satisfy the counit laws `hl` and `hr`. Let `b` be a basis of `I / I²` given by
  classes of `z s ∈ 𝒜 (w s)` with `w s ≠ 0`. Then for `N ≠ 0`, `bigCellMap 𝒜 ε Δ a = 0` implies
  `a ∈ I ^ N`.
* `gradedBigCellInjectivity : GradedBigCellInjectivityStatement.{u}`.

## Proof

Fix `N ≠ 0`. `exists_truncated_section` gives `τ : A → T_N` with `τ x = [p]` whenever
`x ≡ aeval z p` modulo `I ^ N`; then `τ x ≡ ε x` modulo `truncVarIdeal`. Put

* `τ⁻ = truncKeep (w s < 0) ∘ τ`, keeping only the negative-weight variables;
* `τ⁺ = truncKeep (w s > 0) ∘ τ`, keeping only the positive-weight variables.

Both still agree with `ε` modulo `truncVarIdeal`.

*`τ⁺` kills `plusIdeal`.* By `exists_isWeightedHomogeneous_of_section`, a generator `x ∈ 𝒜 d`
with `d ≤ 0` and `ε x = 0` has `τ x = [p]` with `p` weighted-homogeneous of degree `d` and without
constant term. Negative-degree elements have `ε x = 0` by hypothesis. Then
`keepVars_pos_eq_zero` gives `τ⁺ x = 0`. Symmetrically, `τ⁻` kills `minusIdeal`. So `τ⁻` and `τ⁺`
factor through the quotients (`Ideal.Quotient.liftₐ`) as `f⁻` and `f⁺`. Put
`Ψ = productMap f⁻ f⁺ ∘ bigCellMap`. Then `Ψ x = productMap τ⁻ τ⁺ (Δ x)`, by induction on the
tensor `Δ x`.

*`Ψ` is the identity to first order.* By `productMap_sub_mem_sq` and the counit laws,
`Ψ x - τ⁻ x - τ⁺ x + ε x ∈ truncVarIdeal²`. For `x = z s`, `τ (z s) = [X s]`, and since
`w s ≠ 0`, exactly one of `τ⁻ (z s)`, `τ⁺ (z s)` is `[X s]` and the other is `0`. Hence
`Ψ (z s) ≡ X s` modulo `truncVarIdeal²`. For `x ∈ I`, the same relation gives
`Ψ x ∈ truncVarIdeal`.

*Conclusion.* `mem_pow_of_map_eq_zero` (the kernel criterion of `TruncatedSection`) applied to
`Ψ` gives `a ∈ I ^ N` whenever `bigCellMap a = 0`. This proves `mem_pow_of_bigCellMap_eq_zero`.

For `gradedBigCellInjectivity`, choose the homogeneous basis with
`exists_homogeneous_cotangent_basis` (this uses the hypothesis that the degree-zero part of `I`
lies in `I²`). A kernel element lies in `⋂ N, I ^ N`. That intersection is `0` by the Krull
intersection theorem for the proper ideal `I` of the Noetherian domain `A`
(`Ideal.iInf_pow_eq_bot_of_isDomain`).

## Provenance

This is an algebraic version of the statement that the multiplication map `U⁻ × U⁺ → H` is étale
at the identity when the zero weight is absent from the cotangent space. It is modelled on the
open cell of the dynamic method (Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd ed., §2.1).
The proof here uses formal coordinates at the identity instead of the dynamic subgroups. It is an internal lemma for the proof of
`Langlands.GroupScheme.RelativeRoot.TorusActionUnipotenceStatement`.
