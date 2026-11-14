# Reduction of the spherical L-factor generation facts

Author: Worker 8. All declarations are in `Langlands.Conductor`. The module
proves the published `SphericalLFactorGenerationStatement`
([`SphericalLFactorGenerationStatement`](SphericalLFactorGenerationStatement.md))
from five propositions, none of which is proved here:

```lean
theorem sphericalLFactorGeneration_of_ordered
    (hconv : SphericalCorankOneConvergenceStatement.{uF, uV})
    (hlau : UnramifiedCorankOneLaurentStatement.{uF, uV})
    (hgen : OrderedUnramifiedCorankOneGenerationStatement.{uF, uV})
    (hcyc : OrderedUnramifiedSphericalCyclicityStatement.{uF})
    (hreal : OrderedUnramifiedWhittakerRealizationStatement.{uF}) :
    SphericalLFactorGenerationStatement.{uF, uV}
```

- `SphericalCorankOneConvergenceStatement`
  ([`SphericalCorankOneConvergenceStatement`](SphericalCorankOneConvergenceStatement.md)):
  the standard L-polynomial `P` exists and every `Ψ(s, w, W_x)` converges on a
  right half-plane (JPSS 1983, Theorem (2.7)).
- `UnramifiedCorankOneLaurentStatement`
  ([`UnramifiedCorankOneLaurentStatement`](UnramifiedCorankOneLaurentStatement.md)):
  for every `x`, every integral of `π × I(x)` that converges on a right
  half-plane, times `∏_i P(x_i X)`, is a Laurent polynomial (JPSS 1983,
  Theorem (3.1)(ii)). A prospective module
  `UnramifiedCorankOneLaurentFromMultiplicativity` is intended to derive it
  from the general-field multiplicativity statements of JPSS (3.1); that
  successor is not part of this contribution or the published Library.
- `OrderedUnramifiedCorankOneGenerationStatement`
  ([`OrderedUnramifiedCorankOneGenerationStatement`](OrderedUnramifiedCorankOneGenerationStatement.md)):
  for norm-ordered `x`, a finite sum of integrals of `π × I(x)` times
  `∏_i P(x_i X)` is `1` (Jacquet 2012, Lemma 3).
- `OrderedUnramifiedSphericalCyclicityStatement` and
  `OrderedUnramifiedWhittakerRealizationStatement`
  ([`OrderedUnramifiedWhittakerStatement`](OrderedUnramifiedWhittakerStatement.md)):
  Jacquet 2012, Lemmas 1 and 2 with the normalization of the spherical image.

Notation: `W_x = inverseSphericalWhittaker h.conductor.1 h.uniformizer q x`,
`Ψ(s, W, W') = corankOneIntegral ψ abv μ W W' s`, `X = spectralPoint q s`
(`= q^(-s)`), and `Q_x = ∏ i, P.comp (C (x i) * X)`.

## The proof

The proof follows Jacquet 2012, section 1, printed pages 518-519, from Lemma 3
to Lemma 4.

**Symmetry.** `satakeSchur_comp_perm` shows that the Satake Schur value is
unchanged when the parameters are permuted: the product of the parameters is
permuted by `Equiv.prod_comp`, and the Jacobi-Trudi polynomial is symmetric by
the published `jacobiTrudi_isSymmetric` together with
`MvPolynomial.eval_rename`. Hence `sphericalWhittaker_comp_perm` and
`inverseSphericalWhittaker_comp_perm`: `W_(x ∘ σ) = W_x` for every permutation
`σ`. This is Jacquet's remark that `W(x; ψ̄)` is symmetric in `x`.

**Translation.** If `W'(g) = ∑_(t ∈ T) c_t W_0(g t)`, write `W_t` for the
right translate of `W` by `diag(t⁻¹, 1)`. Pointwise on the quotient,
`corankOneIntegrand_eq_sum_translate` rewrites the integrand of `(W, W')` as
the sum of the integrands of `(W_t, W_0)` composed with right translation by
`t`, weighted by `c_t |det t⁻¹|^(s - 1/2)`; it uses the published
`determinantWeight_mul`. `corankOneIntegral_eq_sum_translate` integrates this
identity. It uses `integral_finsetSum` and the right invariance
`hμ.right_invariant t` of the compatible quotient measure; it assumes that
each `(W_t, W_0)` converges at `s`.

**Cyclic vectors.** `exists_finset_translate_of_cyclic`: if `v₀` generates
the representation `ρ`, every function in the coefficient model of `ℓ` is a
finite combination `∑_t c_t f₀(g t)` of right translates of the coefficient
`f₀` of `v₀`. The proof writes the vector as an element of the published
`Cyclic.orbitSpan ρ v₀`, which is the whole space, and expands it with
`Finsupp.mem_span_range_iff_exists_finsupp`.

**Spans of spherical integrals.** `IsSphericalIntegralSpan R` says that `R`
agrees on a right half-plane with `∑_j X^(e_j) Ψ(s, W_j, X₀)` for finitely
many `W_j` in the model of `ℓ` and integers `e_j`. It is closed under zero,
single integrals, sums, finite sums and change on a half-plane, and contains
`κ X^m Ψ(s, w, X₀)` (`corankOneIntegral_smul`).
`exists_determinantWeight_eq_monomial` writes `|det g|^(s - 1/2)` as
`κ X^m`, with `m = ∑ i, exponent h.uniformizer g i`, from the published
`abv_det_eq_zpow_exponent` and `determinantWeight_eq_spectralPoint_zpow`.

`isSphericalIntegralSpan_of_model`: if the spherical section of `I(x)`
generates `I(x)`, the functional `ℓ'` maps it to `W_x`, and every
`Ψ(s, w, W_x)` converges on a right half-plane, then for every `w` in the
model of `ℓ` and every `w'` in the model of `ℓ'`, `s ↦ Ψ(s, w, w')` is a
spherical integral span with `X₀ = W_x`. The translates `W_t` lie in the model
of `ℓ` because the model is a subrepresentation (`modelRepresentation`). This
is Jacquet's "after a change of notations" step.

**Ordered parameters.** For norm-ordered `x`, `laurent_of_ordered` takes `ℓ'`
from `hreal` and `W_x` as an element of its model
(`exists_model_eq_inverseSphericalWhittaker`), and applies `hlau`, with the
assumed convergence of `Ψ(s, w, W_x)` on a right half-plane as the convergence
hypothesis of `hlau`; this is clause 2 of the target at `x`. `generation_of_ordered` applies
`isSphericalIntegralSpan_of_model` (with cyclicity from `hcyc`) to each term
of the finite sum from `hgen`; the result is clause 3 of the target at `x`.

**General parameters.** `exists_perm_monotone_norm` sorts the parameters by
norm with `Tuple.sort` and `Tuple.monotone_sort`. `prod_comp_perm` gives
`Q_(x ∘ σ) = Q_x` by `Equiv.prod_comp`. In
`sphericalLFactorGeneration_of_ordered`, `P` and clause 1 come from `hconv`;
clauses 2 and 3 at `x` are clauses 2 and 3 at `x ∘ σ`, rewritten by
`W_(x ∘ σ) = W_x` and `Q_(x ∘ σ) = Q_x`. The convergence that
`laurent_of_ordered` and `generation_of_ordered` need at `x ∘ σ` is clause 1
at `x`, rewritten in the same way. This is Jacquet's passage from Lemma 3 to Lemma 4.

## Source

H. Jacquet, *A correction to Conducteur des représentations du groupe
linéaire*, Pacific J. Math. 260 (2012), 515-525, literature ID
`jacquet-2012-conductor-correction`, section 1, printed pages 517-519 (Lemmas
1-4 and the remarks between them). The inputs cite JPSS 1983 (literature ID
`jpss-1983-rankin-selberg`), Theorems (2.7) and (3.1)(ii); their Markdown
files give the details.
