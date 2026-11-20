# Proof of matched generation of finite modules over a split square

`Langlands.Analytic.BoundedAlgHom.splitSquareModuleGeneration` proves
`SplitSquareModuleGenerationStatement`. The proof is an internal derivation;
only the axioms `propext`, `Classical.choice` and `Quot.sound` are used.

Notation: `r₁ : A₁ → A₁₂` and `r₂ : A₂ → A₁₂` are the restrictions of the
split square `S`, `c = S.bound`, and `L > 0` is a boundedness constant of `r₂`.
Only three fields of `S` are used: density of `r₂`, the bounded splitting
`S.split`, and its nonnegative constant; the gluing and commutativity fields are
not needed. All matrices are plain functions `Fin n → Fin n → A`; vectors
`Fin n → A` carry Mathlib's supremum norm. No norms on the modules are used.

## Analytic lemmas (namespace `SplitSquareGeneration`)

- `exists_eq_of_approx`: let `T : V →+ W` be continuous with `V` complete. If
  every `w` has some `v` with `‖v‖ ≤ C‖w‖` and `‖w - T v‖ ≤ ‖w‖/2`, then every
  `w` equals `T v` for some `v` with `‖v‖ ≤ 2C‖w‖`. The proof iterates the
  approximation on the residuals, which halve at each step. The corrections sum
  in `V`, and the partial sums of their images telescope to `w` minus a residual
  that tends to zero.
- `norm_sum_mul_le`: `‖∑ₖ fₖ gₖ‖ ≤ n·α·β` under entrywise bounds `α`, `β`.
- `exists_row_solution`: for a matrix `Δ` over `A₁₂` with entries bounded by
  `δ` and `n·L·c·δ ≤ 1/2`, every row `t` is solved by vectors `a` over `A₁` and
  `b` over `A₂`, with `‖aⱼ‖ ≤ 2c‖t‖`, in the sense that
  `r₁ aⱼ + r₂ bⱼ + ∑ₖ r₂(bₖ)Δₖⱼ = tⱼ` for every `j`. It applies
  `exists_eq_of_approx` to the map `(a, b) ↦ r₁ a + (r₂ b)(1 + Δ)` on the
  complete product `(Fin n → A₁) × (Fin n → A₂)`. The approximate solution
  splits `t` entrywise with `S.split`, and its residual `-(r₂ b)Δ` has at most
  half the norm of `t`.
- `exists_left_inverse`: over a complete ring, if the entries of `P` are
  bounded by `η` and `n·η ≤ 1/2`, then `1 + P` has a left inverse `Q`. Each row
  is solved by `exists_eq_of_approx` with the map `q ↦ q + qP`.

## Module lemmas

- `span_image_eq_top`: if `y` generates `M₁` and the image of `u₁` spans
  `M₁₂`, then the vectors `u₁(yᵢ)` span `M₁₂`, by semilinearity of `u₁`.
- `exists_small_identity`: take generators `y` of `M₁` and `x` of `M₂`, and
  write `u₁ yᵢ = ∑ⱼ Dᵢⱼ u₂ xⱼ` and `u₂ xⱼ = ∑ₗ Cⱼₗ u₁ yₗ`. Choose `D'` over
  `A₂` with `‖Dᵢⱼ - r₂ D'ᵢⱼ‖ < δ/κ`, where `κ = ∑‖Cⱼₗ‖ + 1`. Then
  `Δ = -(D - r₂ D')C` has entries of norm at most `δ`, and
  `u₁ yₘ + ∑ₗ Δₘₗ u₁ yₗ = u₂ zₘ` with `zₘ = ∑ⱼ D'ₘⱼ xⱼ`.
- `exists_matched_generating`: solve the rows of
  `r₁ X' + r₂(Y')(1 + Δ) = Δ` by `exists_row_solution`. Set
  `wᵢ = yᵢ + ∑ₗ X'ᵢₗ yₗ` and `w'ᵢ = zᵢ - ∑ₖ Y'ᵢₖ zₖ`. Substituting the row
  equations and the small identity gives `u₁ wᵢ = u₂ w'ᵢ`. The entries of `X'`
  are at most `2cδ`, so `1 + X'` has a left inverse `Q` by
  `exists_left_inverse`, hence `yᵢ = ∑ₖ Qᵢₖ wₖ` and the `w` generate `M₁`.
- `exists_matched_generating_both`: the vectors `u₁ wₖ` span `M₁₂`, so
  `u₂ xⱼ = ∑ₖ eⱼₖ u₁ wₖ`. Split `eⱼₖ = r₁ αⱼₖ + r₂ βⱼₖ`. Then
  `u₁(∑ₖ αⱼₖ wₖ) = u₂(xⱼ - ∑ₖ βⱼₖ w'ₖ)`. The final families are `Fin.append`
  of `(w, w')` and these pairs: the first components contain all `w`, and `xⱼ`
  is a combination of second components.
- `exists_small_constant`: chooses `δ = 1/(4(n+1)(Lc + c + 1))`, which makes
  both smallness conditions hold.

## Main theorem

`splitSquareModuleGeneration` takes finite generators of `M₁` and `M₂`
(`Module.Finite.exists_fin`) and coefficient matrices `D` and `C` from the two
spanning hypotheses. It gets continuity of `r₁` and `r₂` from their bounds,
chooses `δ` by `exists_small_constant`, and chains `exists_small_identity`,
`exists_matched_generating` and `exists_matched_generating_both`.

This is the classical Cartan-lemma argument from the proof of Kiehl's Theorem A
(see the provenance in the statement's Markdown). The classical proof factors
an invertible matrix near the identity multiplicatively. Here that factorization
is replaced by solving a linear equation row by row and then inverting `1 + X'`.
