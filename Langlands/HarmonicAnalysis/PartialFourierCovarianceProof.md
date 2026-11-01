# Proof of elementary covariance of the chosen partial Fourier action

Worker 252 wrote this proof for the adjacent-rank Rankin–Selberg work
coordinated by Worker 486 (parent task `b54b4d62`).

`Langlands.HarmonicAnalysis.partialFourierCovariance` proves the closed
proposition
[`PartialFourierCovarianceStatement.{uK}`](PartialFourierCovarianceStatement.md)
exactly. These are JPSS Section 6.1 formulas (3), (4) and (5). The proof uses
only the proposition's own hypotheses: the field telescope, `ψ`, the supplied
`μ`, the rank `n : ℕ` (zero included) and `hsd : IsSelfDual ψ μ`. It adds no
premise.

## Notation

- `T = partialFourierEquiv ψ μ n hsd` is the chosen last-column transform.
- `R_g = rectangularTranslate g` is right translation, `R_g F m = F (m * g)`.
- `ρ = rectangularRho0 ψ μ n hsd`.
- `ν = rowMeasure μ n`, the product of `n` copies of `μ.measure`.
- `Δ = MeasureTheory.distribHaarChar K`.
- `[x,u]` stands for `rectangularJoin x u`, and `⟨y,u⟩` for `rowPairing y u`.

Two facts from the published
[`PartialFourierEquiv`](PartialFourierEquiv.md) drive the proof.

- `rectangularRho0_apply`: `ρ g Φ = T (R_g (T.symm Φ))`.
- `partialFourierEquiv_apply`: `T F [x,y] = ∫ F[x,u] ψ(-⟨y,u⟩) dν(u)`.

For each of the three kinds of matrix `g`, the proof first shows an identity
`T (R_g F) = L (T F)` for every Schwartz function `F`, where `L` is an explicit
operation. Applying it to `F = T.symm Φ` and cancelling `T (T.symm Φ) = Φ`
(`LinearEquiv.apply_symm_apply`) gives `ρ g Φ = L Φ`, which is the law.

## Matrix identities

`rectangularJoin_mul_apply` writes an entry of `[x,u] M` as
`∑ k, x i k * M k.castSucc j + u i * M (last n) j`. It splits the sum over
`Fin (n + 1)` with `Fin.sum_univ_castSucc`. The entries of the published
elementary matrices are read off as follows.

- For `blockSum`, use the published `blockSum_apply_*` lemmas. Here
  `castSucc` is `castAdd 1`, and `last n` is `natAdd n 0`.
- `GeneralLinear.rankInclusion 1 h` is `blockSum (h, 1)` by definition.
- For `blockUnipotent`, an entry of its value is by definition the entry of
  `fromBlocks 1 X 0 1` at `finSumFinEquiv.symm` of the indices. Mathlib's
  `finSumFinEquiv_symm_apply_castSucc` and `finSumFinEquiv_symm_last`
  evaluate these indices.

The resulting identities are:

- `rectangularJoin_mul_rankInclusion`: `[x,u] · diag(h,1) = [x h, u]`;
- `rectangularJoin_mul_blockUnipotent`: `[x,u] · [[I_n, v],[0,1]] = [x, x v + u]`,
  with `x v = Matrix.mulVec x v`;
- `rectangularJoin_mul_lastScalar`: `[x,u] · diag(I_n, a) = [x, a u]`, where
  `a u` is the vector `fun i => a * u i`;
- `blockSum_lastScalar_inv`: `diag(I_n, a)⁻¹ = diag(I_n, a⁻¹)`, because
  `blockSum` and `scalar` are group homomorphisms.

## Measure facts on the actual `rowMeasure μ n`

None of the following uses integrability, a Borel structure on the product,
or second countability. Sigma-finiteness of `μ.measure` is derived from `hsd`
by the published `selfDualSigmaFinite`
([`SelfDualSigmaFiniteProof`](SelfDualSigmaFiniteProof.md)).

- **Translation** (`integral_rowMeasure_add_left`). For every `c` and every
  function `f`, `∫ f (c + w) dν = ∫ f dν`. Mathlib's instance
  `Measure.pi.isAddLeftInvariant` makes `ν` left invariant. It applies because
  each factor `μ.measure` is a sigma-finite Haar measure and addition on `K`
  is measurable. Translation on the product is measurable by
  `Pi.measurableAdd`. Then `integral_add_left_eq_self` applies.
- **Scalar pushforward** uses the published
  `map_mul_left_eq_inv_distribHaarChar` from
  [RectangularFourierCovarianceProof](RectangularFourierCovarianceProof.md).
  Multiplication by a unit `a` pushes `μ.measure` forward to
  `Δ(a)⁻¹ • μ.measure`. The preimage of `t` is `a⁻¹ • t`, and Mathlib's
  `distribHaarChar_mul` applies because `μ` is a regular Haar measure.
- **Product scaling** (`rowMeasure_map_mul_left`). Coordinatewise
  multiplication by `a` pushes `ν` forward to `(Δ(a)⁻¹)^n • ν`. Mathlib's
  `Measure.pi_map_pi` turns the pushforward of the product into the product of
  the pushforwards, using the scalar pushforward on each factor. The published
  `pi_nnreal_smul` ([`FiniteProductMeasureScaling`](FiniteProductMeasureScaling.md))
  then pulls the constant scalars out as `∏ i : Fin n, Δ(a)⁻¹ = (Δ(a)⁻¹)^n`.
- **Scaling change of variables** (`integral_rowMeasure_mul_left`). For every
  function `f`, `∫ f (a w) dν = ((Δ(a))^n)⁻¹ * ∫ f dν` in `ℂ`. The scaling map
  is the measurable equivalence
  `MeasurableEquiv.piCongrRight (fun _ => MeasurableEquiv.mulLeft₀ a _)`. So
  `MeasurableEmbedding.integral_map` applies to every `f`. The constant comes
  out by `integral_smul_nnreal_measure`.

## The three intertwining identities

**Formula (3)** (`partialFourierEquiv_translate_rankInclusion`):
`T (R_g F) = R_g (T F)` for `g = diag(h,1)`, as Schwartz functions. At
`[x,y]` both sides are `∫ F[x h, u] ψ(-⟨y,u⟩) dν(u)`. The integrand of the
left side is rewritten pointwise by `[x,u] g = [x h, u]`. The right side
evaluates `T F` at `[x,y] g = [x h, y]`. No change of variables is used.

**Formula (4)** (`partialFourierEquiv_translate_blockUnipotent`): for the
unipotent `u_v = [[I_n,v],[0,1]]` and `c = x v`,

```text
T (R_{u_v} F) [x,y] = ∫ F[x, c + u] ψ(-⟨y,u⟩) dν(u)
                    = ∫ G (c + u) dν(u)
                    = ∫ G dν
                    = T F [x,y] * ψ(⟨y, c⟩),
```

with `G w = F[x,w] ψ(-⟨y,w⟩) ψ(⟨y,c⟩)`. The second equality is pointwise. It
uses `⟨y, c + u⟩ = ⟨y,c⟩ + ⟨y,u⟩` and the character law
`AddChar.map_add_eq_mul`. The third is translation invariance. The last pulls
out the constant with `integral_mul_const`.

**Formula (5)** (`partialFourierEquiv_translate_lastScalar`): for
`d = diag(I_n, a)`,

```text
T (R_d F) [x,y] = ∫ F[x, a u] ψ(-⟨y,u⟩) dν(u)
                = ∫ G (a u) dν(u)
                = ((Δ(a))^n)⁻¹ * ∫ G dν
                = ((Δ(a))^n)⁻¹ * T F [x, a⁻¹ y],
```

with `G w = F[x,w] ψ(-⟨a⁻¹ y, w⟩)`. The second equality is pointwise, using
`⟨a⁻¹ y, a u⟩ = ⟨y,u⟩`. The third is the scaling change of variables. The
point `[x, a⁻¹ y]` is `[x,y] d⁻¹` by the identities for `d⁻¹` and
`diag(I_n, a⁻¹)`.

## Assembling the theorem

- **Law 1** rewrites `ρ g Φ` by `rectangularRho0_apply`, then applies
  formula (3) with `F = T.symm Φ`, then cancels `T (T.symm Φ)`.
- **Law 2** does the same with formula (4), evaluated at `[x,y]`.
- **Law 3** is checked pointwise, after writing each matrix as `[x,y]` with
  `rectangularJoin_split`. Formula (5) and the cancellation give
  `((Δ(a))^n)⁻¹ * Φ[x, a⁻¹ y]`. The right side of the law evaluates by
  definition to `((Δ(a))^n)⁻¹ * Φ ([x,y] d⁻¹)`, and the matrix identities
  turn this into the same value.

The scalar in Law 3 comes out of the proof as stated: the inverse of the
`n`-th power of the real Haar character, cast to `ℂ`. For `n = 0` every sum
and product above is empty. The same proof applies without a case split.

## Scope

The proof uses the published elementary matrices, the chosen transform
`partialFourierEquiv` with its inverse character, the actual whole-matrix
Schwartz space and the supplied measure `rowMeasure μ n`. Its only new public
declarations are the matrix identities, the three measure facts and the three
intertwining identities above. It does not prove formula (2), which the input
already proves as `rectangularRho0_intertwine`. It also does not prove full
Fourier covariance, the full/partial commutation, formula (7), or any
vector-valued integral model.

## Source

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg
Convolutions*, Amer. J. Math. 105 (1983), Section 6.1, formulas (3)–(5),
printed page 428. This is registered source `jpss-1983-rankin-selberg`
(one-based PDF page 63). The source says these formulas are easily deduced.
The computation above is the evident deduction, carried out for the generic
Haar character `Δ` described in the statement's Markdown.
