# Rectangular Fourier slices of last-row cutoffs

Worker 731 authored this derived harmonic-analysis statement. The module
contains one Prop-valued definition and no proof.

## The statement

`Langlands.HarmonicAnalysis.PadicMatrixFourierSliceStatement.{u}` is a closed
proposition. For every prime `p`, every `F : PadicField.{u} p`, every
`T : F.TopologicalData` and all `a b : ℕ`, it assumes

```
PadicRowFourierSurjectivityStatement F T (b + 1)
```

(row Fourier surjectivity in dimension `b + 1`, from
`HarmonicAnalysis.PadicRowFourierSurjectivityStatement`). It then installs
exactly `T.topology` on `F.Carrier` and the Borel measurable space of that
topology. For every `ψ : UnitaryAdditiveCharacter F.Carrier`, every
`ν : AdditiveHaarMeasure F.Carrier` and every
`Φ : SchwartzBruhat (Fin (b + 1) → F.Carrier)` it asserts that some
`Ψ : SchwartzBruhat (Matrix (Fin (b + 1)) (Fin (a + 1)) F.Carrier)`
satisfies, for every `g : GeneralLinear (b + 1) F.Carrier`,

```
∫ x, ψ.complex (-(x (Fin.last b) 0)) * Ψ (g⁻¹.val * x)
    ∂RankinSelberg.rectangularMeasure ν (b + 1) (a + 1)
  = (T.normalizedAbs (det g.val) : ℂ) ^ (a + 1) * Φ (RankinSelberg.lastRow g).
```

Conventions:

- `x` ranges over matrices with `b + 1` rows and `a + 1` columns.
  `x (Fin.last b) 0` is the entry in the last row and first column.
  The character factor is `ψ` of the negative of that entry: no conjugation,
  only the sign.
- `g⁻¹.val * x` is ordinary matrix multiplication by the inverse of `g`, so
  `GL_{b+1}` acts on the left of the rectangular space.
- The measure `RankinSelberg.rectangularMeasure ν (b + 1) (a + 1)` is the
  published finite product of the supplied scalar Haar measure `ν` over all
  entries. No self-dual or other normalization of `ν` is selected.
- `T.normalizedAbs` is the published normalized absolute value
  `q^(-ord x)`, coerced from `ℝ` to `ℂ`, raised to the natural power `a + 1`.
- `RankinSelberg.lastRow g` is the last row `j ↦ g (Fin.last b) j` of `g`.
- The integral is the Bochner integral. The statement does not separately
  assert integrability.

`Ψ` depends on `ψ`, `ν` and `Φ`, but is the same for all `g`.

## Source and provenance

The source is Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg
Convolutions*, Amer. J. Math. 105 (1983), registered as
`jpss-1983-rankin-selberg` (retained PDF
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`).
The Proposition of Section (9.1) and its proof are on printed pp. 453–454 (PDF
pp. 88–89), which were read visually. No errata note for this source is
registered.

In that proof, with `r₁ = a + 1` and `r₂ = b + 1`, the Whittaker function of
the induced vector at `diag(g, 1_{r₁})` is written as
`W₁(e) ∫ Ψ[g⁻¹ x] W₂(g) |det g|^{-r₁/2} θ̄(u(x)) dx`, where `u(x)` is the block
upper unipotent matrix with off-diagonal block `x ∈ M(r₂ × r₁)`. The only
superdiagonal entry of `u(x)` inside the block `x` is its last-row, first-column
entry, so `θ̄(u(x)) = ψ(-x_{r₂,1})`, the factor in the Lean integrand.
After the change of variables `x ↦ g x`, whose Jacobian is `|det g|^{r₁}`,
JPSS obtain `W₁(e) W₂(g) |det g|^{r₁/2} Φ'[-μ g]` with
`Φ'(y) = ∫ Ψ(x) ψ(tr(y x)) dx`, and conclude "Our assertion is therefore
clear". That conclusion uses, without separate statement, that `Ψ` can be
chosen so that `Φ'[-μ g] = Φ[η_{r₂} g]` for the given cutoff `Φ`.

This module isolates exactly that scalar step. The Lean identity is the JPSS
integral without the factors `W₁(e) W₂(g) |det g|^{-r₁/2}`; its right side
`|det g|^{r₁} Φ(η_{r₂} g)` is the Jacobian times the required cutoff, and
`η_{r₂} g` is the last row of `g`. The formulation is derived:

- it asks only for one `Ψ` realizing a given `Φ`, not for bijectivity of a
  rectangular Fourier transform;
- the needed Fourier surjectivity is an explicit hypothesis, the existing
  published proposition `PadicRowFourierSurjectivityStatement F T (b + 1)`
  for the same `F` and `T`; this module does not assume or prove it, and a
  consumer needing an unconditional result must discharge it;
- the measure is the product of an arbitrary scalar Haar measure, so no
  self-dual normalization from the source is imposed;
- the field topology is an arbitrary supplied `T : F.TopologicalData`, which
  specializes to `F.canonicalTopologicalData` used by
  `Whittaker.TwoBlockWhittakerExtensionStatement`.

The intended consumer is the proof of
`Langlands.Whittaker.TwoBlockWhittakerExtensionStatement`, whose scalar Jacquet
kernel at the relevant unipotent element equals the character factor above.
