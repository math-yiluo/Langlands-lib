# Generation by corank-one integrals of `π × I(x)` for norm-ordered `x`

This module defines one proposition,
`Langlands.Conductor.OrderedUnramifiedCorankOneGenerationStatement`
(universes `uF`, `uV`). It is a statement only: nothing here proves it.

## Statement

The binders start as those of the published
`Langlands.Conductor.SphericalLFactorGenerationStatement`
([`SphericalLFactorGenerationStatement`](SphericalLFactorGenerationStatement.md)),
in the same order: a nonarchimedean local field `F : Type uF` of any
characteristic, `n : ℕ`, the measurable and Borel structures, `q`, `ψ`, `abv`,
`ϖ`, `μ`, `h : IsJacquetNormalization q ψ abv ϖ μ`, `V : Type uV`, a
representation `π` of `GL_(n+2)(F)` on `V` with `IsGeneric ψ (n + 1) π`, and
`ℓ : glFunctionals ψ (n + 1) π` with `ℓ.val ≠ 0`. They continue with

- `P : ℂ[X]` with `IsCharacterLPolynomial q ψ abv (rankOneQuotientHaar F) 1 π P`
  (`L(s, π × 1) = P(q^(-s))⁻¹`, `P(0) = 1`);
- `x : Fin (n + 1) → ℂˣ` with `Monotone (fun i => ‖(x i : ℂ)‖)`, that is
  `|x_1| ≤ ⋯ ≤ |x_(n+1)|`;
- `ℓ' : glInverseFunctionals ψ n ρ` with `ℓ'.val ≠ 0`, where
  `ρ = principalSeries h.uniformizer n h.residueCardinality x` is the published
  normalized unramified principal series `I(x)` of `GL_(n+1)(F)`
  ([`UnramifiedPrincipalSeries`](UnramifiedPrincipalSeries.md)). `ℓ'` is a
  Whittaker functional for the inverse character `ψ̄`.

Write `Ψ(s, W, W')` for `corankOneIntegral ψ abv μ W W' s`, `X = q^(-s)` for
`spectralPoint q s`, and `Q_x = ∏ i, P.comp (C (x i) * X)`, the polynomial
`∏_i P(x_i X)`. The conclusion: there are `k : ℕ`,
`W : Fin k → coefficientModel π ℓ`, `W' : Fin k → coefficientModel ρ ℓ'` and
`a : ℝ` with `(∑_j Ψ(s, W_j, W'_j)) · Q_x(q^(-s)) = 1` for every `s` with
`a < Re s`.

With `x_i = q^(-t_i)`, `P(x_i q^(-s))⁻¹ = L(s + t_i, π)`. So the statement
says that `∑_j Ψ(s, W_j, W'_j) = ∏_i L(s + t_i, π)` on a right half-plane. It
does not assert convergence. The identity concerns the published
`corankOneIntegral` values on the half-plane.

## Source

Jacquet 2012 (*A correction to Conducteur des représentations du groupe
linéaire*, Pacific J. Math. 260 (2012), 515-525, literature ID
`jacquet-2012-conductor-correction`), section 1, printed pages 517-519. There
`t = (t_1, …, t_(r-1))` satisfies `Re(t_1) ≥ ⋯ ≥ Re(t_(r-1))` (printed page
517). Since `|x_i| = q^(-Re t_i)` and `q > 1`, this is the norm order above.
Jacquet's Lemma 3 (printed page 519), quoted from JPSS 1983
(H. Jacquet, I. I. Piatetski-Shapiro, J. A. Shalika, *Rankin-Selberg
convolutions*, Amer. J. Math. 105 (1983), 367-464, literature ID
`jpss-1983-rankin-selberg`), states: there are `W_j` in the Whittaker model of
`π` and `W'_j` in the `ψ̄`-Whittaker model of `I(t)` with
`∑_j Ψ(s, W_j, W'_j) = ∏_i L(s + t_i, π)`. The statement is the product form
of this identity (with `r = n + 2`). In JPSS 1983 it is part of the
computation of `L(s, π × π')` for `π'` induced in Langlands order (Section 9,
Theorem (9.4), which uses (8.4)). The norm order on `x` is that Langlands
order.

The Lean statement quantifies over every nonzero `ψ̄`-Whittaker functional
`ℓ'`. Jacquet uses one such functional (printed page 518). The space of these
functionals on `I(t)` is one-dimensional, so all choices give the same model.

## Over p-adic fields, and the general case

**Over p-adic fields.** The Library proves the p-adic form of this proposition.
The published `PadicOrderedUnramifiedCorankOneGenerationStatement`
([`PadicOrderedUnramifiedCorankOneGenerationStatement`](PadicOrderedUnramifiedCorankOneGenerationStatement.md))
is this proposition with the field `K.Carrier` of a p-adic field `K` and its canonical
structures. `Langlands.Conductor.padicOrderedUnramifiedCorankOneGeneration`
([`PadicOrderedUnramifiedCorankOneGenerationProof`](PadicOrderedUnramifiedCorankOneGenerationProof.md))
proves it.

**The general case.** JPSS 1983 takes as ground field an arbitrary nonarchimedean local
field ((0.3), printed page 375), so the gap below is one of the Lean formalization. Over
an arbitrary nonarchimedean local field `F`, of any characteristic, the Library gives a
conditional proof of the proposition at `F` from the following three hypotheses at `F`,
results of JPSS 1983, §§8–9
(`Conductor.orderedUnramifiedCorankOneGenerationAt_of_premises`, module
[`OrderedUnramifiedGenerationFromPremises`](OrderedUnramifiedGenerationFromPremises.md);
`Conductor.orderedUnramifiedCorankOneGeneration_of_premises` for every field at once).
They are stated in
`Langlands.AllField.Representation.RankinSelberg.TemperedTypePremisesStatement`:

1. the Langlands classification of generic representations, with the equality of the
   Whittaker functions of `π` and of its standard module (`GenericStandardModuleStatement`;
   JPSS 1983, (9.4), printed page 458);
2. the tempered pole bound (`TemperedPoleBoundStatement`; JPSS 1983, (8.4), printed pages
   451–452);
3. the tail divisibility (`InducedTailLFactorAt`; JPSS 1983, (9.3), printed pages
   455–457).

The fourth input is the product formula of JPSS 1983, (9.4), printed pages 458–462. The
theorem `Langlands.AllField.RankinSelberg.temperedTypeLPolynomial_product` proves the
(9.4) product for standard modules from (8.4) and (9.3) over the given field. The theorem
`Langlands.Conductor.OrderedUnramifiedTemperedType.lPolynomial_principalSeries_eq_prod`
applies this product to `π × I(x)`, using the Whittaker identification in
`GenericStandardModuleStatement`. The Library proves the three hypotheses over p-adic
fields, from its p-adic classification results
(`Langlands.Representation.RankinSelberg.PadicTemperedTypePremises`). In the Lean
formalization, the general case lacks the all-field forms of these results and nothing
else.

As measured on the Library at commit `2cda61ad`, the import closures of the p-adic proofs
of these results contain about 807 modules that mention the p-adic field and have no
all-field port, about 150,000 lines in all. Of these:

- the coverage theorem of the classification needs 121;
- (9.3) needs 124 more;
- the tempered results behind (8.4) and the genericity of tempered blocks need 532 more;
- the assembly of (9.4) needs 30 more.

The classification cannot be bypassed by a direct induction on `I(x)`: one that uses
(9.3), (3.1) and the functional equation, but not the Langlands structure of `π`. Its
step needs the poles of `L(s + t_1, π)` and of `L(1 - s - t_2, π~)` to be disjoint, and
this can fail. Take `π = ν^u × ν^(-u) × 1` on `GL_3` with real `u > 1/2` and `u ≠ 1`, so
that `π` is irreducible and generic and `L(s, π) = ζ_F(s + u) ζ_F(s - u) ζ_F(s)` with
`ζ_F(s) = (1 - q^(-s))⁻¹`. Here `n = 1` and `I(x) = I(t_1, t_2)` with `x_i = q^(-t_i)`.
When `t_1 - t_2 = 2u - 1`, which the order `Re t_1 ≥ Re t_2` allows, the point
`s = u - t_1 = 1 - t_2 - u` is a pole of both, so the direct step does not reach
`L(s, π × I(x)) = L(s + t_1, π) L(s + t_2, π)`. JPSS 1983, (9.4), printed pages 458–462,
separates the possible poles after passing to the tempered blocks of the standard module
of `π`, using the classification, (8.4) and (9.3). Jacquet 2012, printed page 519,
recalls the resulting generation identity as Lemma 3 and uses cyclicity and symmetry to
derive Lemma 4.
