# Unconditional convergence of the JPSS Section 6.1 tensor integral

Worker 455 states the first assertion of the Proposition in Section 6.1
of Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg convolutions*,
Amer. J. Math. 105 (1983), printed pp.428–429, formula (8).
The registered original is `jpss-1983-rankin-selberg`, retained at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The original printed pp.427–431 and the inverse-transpose convention
(0.3.6) on p.376 were visually inspected. No source-specific errata file
was found in the project's prescribed errata locations.

`Langlands.RankinSelberg.AdjacentRankModelConvergenceStatement.{uF,uV}`
is a closed, `Prop`-valued definition. **It is an unproved proposition
definition, not a convergence theorem.** Its sole import is the published
`Langlands.Representation.RankinSelberg.AdjacentRankIntegralModel`.
It leaves that module and every other published Lean/Markdown pair
unchanged. The mathematical assertion comes from the cited Proposition;
the explicit canonical p-adic telescope and finite algebraic tensor
formulation use the Library's existing realization.

## Quantifiers and conclusion

The proposition quantifies over every prime `p`, every
`F : PadicField.{uF} p`, every
`ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier`, every supplied
`ν : HarmonicAnalysis.AdditiveHaarMeasure F.Carrier`, and every supplied
`hself : HarmonicAnalysis.IsSelfDual ψ ν`. The character structure already
includes continuity and nontriviality.

Inside the proposition, local instances give `F.Carrier` its canonical
topology, valuative relation and local field structure, its Borel measurable
structure, and the canonical Hausdorff and totally disconnected structures.
The latter follows from the nonarchimedean valuation topology, as in the
imported model. These are constructions from the canonical field data,
not additional hypotheses.

For every `r : ℕ`, every `V : Type uV` with `[AddCommGroup V] [Module ℂ V]`,
and every actual representation
`σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V`, the premise is
the published full Whittaker-type predicate

```text
Langlands.RankinSelberg.IsOfWhittakerType
  r (Langlands.Whittaker.standardCharacter ψ r) σ.
```

This is the existing declaration from `AnalyticStatement`: admissibility,
finite generation over the group algebra, and a one-dimensional space of
functionals for the standard character. It permits reducible
representations. The Whittaker-type predicate lives in
`Langlands.RankinSelberg`; the standard character and functionals live in
`Langlands.Whittaker`.

For every `ℓ : Whittaker.glFunctionals ψ r σ`, every continuous
`χ : HarmonicAnalysis.Quasicharacter F.Carrier`, every
`Ψ : adjacentRankTestSpace ψ σ ℓ`, and every
`g : GeneralLinear (r + 2) F.Carrier`, the conclusion is exactly

```text
Langlands.RankinSelberg.Padic.AdjacentRankModelConverges
  F ψ ν hself σ ℓ χ Ψ g.
```

The universes `uF` and `uV` are independent. There is no topology, norm or
completeness on `V` or the coefficient image. The functional `ℓ` may be
zero; no nonvanishing premise is added. Rank `r = 0` is included, with
inner group `GL₁` and ambient group `GL₂`. There is no irreducibility,
large twist, character norm bound, coefficient-growth or convergence
premise, factor-existence premise, or assumption about an induced model.

## The exact integral being asserted to converge

Write `T = r + 2` for the source's ambient rank `t`. The inner group is
`GL_(T-1) = GL_(r+1)`. The imported test space is the algebraic complex
tensor product

```text
SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier) ⊗[ℂ]
  (Whittaker.glCoefficientModel ψ r σ ℓ).toSubmodule.
```

It realizes the source's Schwartz functions with values in the actual
Whittaker coefficient image of `ℓ`. Every tensor is a finite sum
`∑ Φⱼ ⊗ Wⱼ`, evaluated at `(m, k)` as
`∑ Φⱼ(m) Wⱼ(k)`. The proposition quantifies over all tensors, with no
restriction to pure tensors and no topological tensor completion.
The published `adjacentRankRho0` acts through `rectangularRho0` on the
Schwartz factor and the identity on the coefficient factor. It uses the
chosen partial Fourier equivalence for the supplied `ψ`, `ν` and `hself`.

For `h : GL_(r+1)`, let `ε` be the last standard basis column and
`h^ι = (h⁻¹)ᵀ`, as in JPSS (0.3.6). The kernel is the actual rectangular
matrix `[h, h^ι ε]`; the coefficient variable is `h⁻¹`. Its last column
has entries `(h⁻¹)(last, i)`. If `E` denotes
`adjacentRankTestEvaluation ψ σ ℓ`, the scalar inner integrand is

```text
h ↦ E (adjacentRankRho0 ψ ν hself σ ℓ g Ψ) [h, h^ι ε] h⁻¹
      * χ(det h) * |det h|^(r/2).
```

The existing p-adic convergence predicate is literally complex Bochner
`Integrable` for this integrand with
`normalizedAbsoluteValue F.canonicalTopologicalData` and exactly
`generalLinearHaar F.Carrier r` on the inner `GL_(r+1)`. This shared Haar
measure gives the integral subgroup mass one. Its Borel data are fixed
by the imported p-adic wrapper. No other measure or Fourier equivalence
is selected. The outer factor of formula (8) is
`χ(det g) |det g|^((r+1)/2)`; the inner exponent is `r/2`, since
`T/2 - 1 = r/2`. The conclusion asserts ordinary absolute integrability
of the inner scalar function, not a rational continuation, truncated
integral or existentially chosen value.

## Why no positive-twist restriction appears

On p.429 the Proposition first asserts convergence of formula (8).
Its separate second assertion identifies and spans the induced Whittaker
model when the real twist parameter is sufficiently large and positive.
The source introduces that parameter on p.427, but its first convergence
argument does not use a lower bound on it.

For convergence the source absorbs `ρ₀(g)` into the test function, reduces
to decomposable Schwartz and Whittaker factors, and uses their compact
invariance to apply Iwasawa decomposition. The Whittaker gauge bounds
inverse diagonal coordinates, while compact support of the Schwartz
factor bounds the diagonal coordinates in the other direction. Thus
the diagonal coordinates stay bounded away from zero and infinity,
and the unipotent variable also stays in a compact set. This gives
convergence for an arbitrary quasicharacter. By contrast, the
induced-model argument on pp.430–431 invokes a sufficiently large
positive twist for absolute convergence of the separate double
integral (13). Page 431 explicitly uses the finite-sum decomposition
of arbitrary tensors.

This Markdown describes the source's convergence route only; this Lean
module implements no analytic proof. Model membership, spanning,
equivariance, star transforms, analytic identities, and gamma or L
factors remain separate obligations. No unrestricted two-block
multiplicativity assertion or parent theorem is imported or assumed.
