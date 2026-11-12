# Bounded wave packets of Eisenstein series

Module `Langlands.Global.AdelicBoundedWavePacketStatement` states Lapid's
Lemma 10 as `Langlands.Global.BoundedWavePacketStatement`, the conjunction of
two proposition definitions:

- `Langlands.Global.BoundedWavePacketInnerProductStatement`, Proposition 2
  for bounded measurable wave packets supported where the Eisenstein series
  are regular;
- `Langlands.Global.BoundedWavePacketNormBoundStatement`, the bound (19).

It supplies no proofs.

## Source

E. Lapid, *On Arthur's asymptotic inner product formula of truncated
Eisenstein series*, in: On Certain L-Functions, Clay Math. Proc. 13 (2011),
pp. 309–331, registered as
`lapid-2011-asymptotic-inner-product-truncated-eisenstein` (volume PDF; PDF
page = printed page + 9).

- §3, p.314: `W_P`, the norm (3) `‖φ‖²_* = ∫_{i𝔞_P^*} ‖φ(λ)‖²_P dλ`, the
  wave packet `Θ_φ(g) = ∫_{i𝔞_P^*} E_P(g, φ(λ), λ) dλ`, and Proposition 2
  with formula (4)
  `(Θ_{P,φ}, Θ_{P',φ'}) = ∫_{i𝔞_P^*} ∑_{w ∈ Ω(P, P')} (M(w, λ)φ(λ), φ'(wλ))_{P'} dλ`.
- §8, Lemma 10, p.329: "Suppose that `φ` is a bounded measurable function
  from `i𝔞_P^*` into a finite-dimensional space `V` of `A^2_P`. Suppose that
  `φ` is supported in a compact set `C` on which `E_P(ψ, ·)` is regular for
  all `ψ ∈ V`. Similarly for `φ'`. Then Proposition 2 holds for `φ, φ'`. In
  particular, we have (19) `‖Θ_φ‖²_{L²(G \ G(𝔸))} ≤ |Ω| ‖φ‖²_*`."
- Lapid's proof of Proposition 6 (pp.329–330) uses (19) for wave packets
  supported near a possible pole of `E_P(·, φ₀, λ)` on `i𝔞_P^*`. The
  published `WavePacketInnerProductStatement` asks the Eisenstein series to be
  holomorphic on all of `i𝔞_P^*`, so it cannot serve there; this module states
  the form Lapid uses.

## Statements

### `BoundedWavePacketInnerProductStatement`

The data are those of `WavePacketInnerProductStatement` (see its Markdown),
with these changes:

- the coefficients `c j : ℝⁿ → ℂ` are measurable, bounded
  (`∃ C, ∀ x, ‖c j x‖ ≤ C`) and zero outside a compact set `S ⊆ ℝⁿ`, instead
  of smooth with compact support;
- the continuations `E j` are meromorphic with a domain of holomorphy `D`
  containing `{i e(x) | x ∈ S}`, instead of all of `i𝔞_P^*`;
- the coefficients `coeff t j i` of the intertwining operators are
  meromorphic with a domain of holomorphy `DM` containing `{i e(x) | x ∈ S}`;
- the same for `P'`: `c' j` measurable, bounded and zero outside a compact
  `S' ⊆ ℝ^{n'}`, and `D' ⊇ {i e'(x') | x' ∈ S'}`.

The conclusion is that of `WavePacketInnerProductStatement`: `y ↦ Θ(y.out)`
and `y ↦ Θ'(y.out)` lie in `L²(G(F) \ G(𝔸), μG)`, and
`∫ Θ(y.out) · conj Θ'(y.out) dμG(y)` equals
`∫ ∑ t, ∑ j, ∑ i, ∑ j', c j x · coeff t j i (i e(x)) · conj (c' j' (x'_t)) · (ψ t j i, v' j')_{P'} d(spectralMeasure n)(x)`,
with `x'_t = e'⁻¹(w_t e(x))`.

### `BoundedWavePacketNormBoundStatement`

The data, for a number field `F : Type`:

- `G` connected reductive; `P = MU` with presentation
  `r : ParabolicRootPresentation p l a`, `p` and `iU ≫ p` closed immersions,
  `iU` a geometric unipotent radical, all groups affine, `M` locally of
  finite type, and a Levi projection `π : P → M` with `l ≫ π = 𝟙`;
- `K` maximal compact with `P(𝔸)K = G(𝔸)`, a closed matrix embedding `rho`,
  and the smooth-structure data `hsmooth`, `hcalc`;
- a Haar measure `μM` on `M(𝔸)` with
  `IsIwasawaCompatibleMeasure K hK.isCompact p iU l μM`;
- a linear isomorphism `e : ℝⁿ ≃ X^*(P) ⊗ ℝ` and a continuous compactly
  supported `β : ℝⁿ → ℝ` with `∫ β = 1`, defining
  `(·,·)_P = inducedInnerProduct K hK.isCompact p l μM e β`;
- `v j ∈ A^2_P` (`IsSquareIntegrableInducedForm`), coefficients `c j`
  measurable, bounded and zero outside a compact set `S`, and `E`, `D` with
  `{i e(x) | x ∈ S} ⊆ D`, every `λ ↦ E j λ g` meromorphic with domain of
  holomorphy `D`, and `E j λ = hK.eisensteinSeries (v j) λ` for `Re λ`
  sufficiently regular.

Let `Θ(g) = ∫ ∑ j, c j x · E j (i e(x)) g d(spectralMeasure n)(x)`,
`φ(x) = ∑ j, c j x · v j`, and `μG` the quotient of Mathlib's Haar measure on
`G(𝔸)` by counting measure on `G(F)`. The conclusion:

1. `weylParameterSet p l p l π`, that is `Ω(P, P)`, is finite;
2. `y ↦ Θ(y.out)` is in `L²(G(F) \ G(𝔸), μG)`;
3. `∫ ‖Θ(y.out)‖² dμG(y) ≤ |Ω(P, P)| · ∫ Re (φ(x), φ(x))_P d(spectralMeasure n)(x)`.

## Correspondence with the source

- Bounded measurable `φ`. A bounded measurable `φ` from `i𝔞_P^*` to a
  finite-dimensional `V ⊆ A^2_P`, supported in a compact `C`, is
  `∑ j, c j · v j` for a basis `v j` of `V`, with `c j` bounded, measurable
  and zero outside `C`. Here `c j` is written in the coordinates
  `λ = i e(x)` and `C` corresponds to `S`.
- Regularity on the support. "`E_P(ψ, ·)` is regular on `C` for all
  `ψ ∈ V`" means that `E(v j, ·)` is holomorphic near `C` for each basis
  vector, which is `{i e(x) | x ∈ S} ⊆ D` with `D` open. The continuations
  enter in universal form, as in the published Bernstein–Lapid statements.
  The intertwining operators are holomorphic on all of `i𝔞_P^*`
  (`IntertwiningImaginaryUnitarityStatement`), so asking for `coeff t j i`
  holomorphic only near the support is a weakening of the hypotheses, and
  only those values enter the formula, since `c j` vanishes outside `S`. On
  `S` the integrands are continuous in `λ` times bounded measurable
  coefficients; outside `S` they vanish, whatever values `E j` or
  `coeff t j i` take outside their domains.
- "Proposition 2 holds for `φ, φ'`" is the conclusion of
  `BoundedWavePacketInnerProductStatement`, with the conventions of
  `WavePacketInnerProductStatement` for `Ω(P, P')`, `M(w, λ)`, the measures,
  the regions, the compact subgroup and the parabolics. Every `φ ∈ W_P`
  whose Eisenstein series are holomorphic near its support is covered, so
  this statement contains `WavePacketInnerProductStatement`.
- The norm (3). For `λ = i e(x)`, `φ(λ) = ∑ j, c j x · v j` and
  `‖φ(λ)‖²_P = Re (φ(x), φ(x))_P`; with `dλ = spectralMeasure n`,
  `‖φ‖²_* = ∫ Re (φ(x), φ(x))_P d(spectralMeasure n)(x)`. The real part is
  taken only to compare real numbers; the inner product of `φ(x)` with
  itself is real.
- The constant `|Ω(P, P)|`. Lapid writes `|Ω|`, the order of the Weyl group
  `Ω = N_G(T₀)/M₀` of `G` (§2). The bound comes from (4) with `φ' = φ`:
  `‖Θ_φ‖² = ∫ ∑_{s ∈ Ω(P, P)} (M(s, λ)φ(λ), φ(sλ))_P dλ`, and each term is at
  most `‖φ‖²_*` by the Cauchy–Schwarz inequality, the unitarity of
  `M(s, λ)` on `i𝔞_P^*`, and the invariance of `dλ` under `λ ↦ sλ`
  (`Ω(P, P)` is a finite group, so `|det s| = 1`). This gives the factor
  `|Ω(P, P)|`, which is at most `|Ω|` because every element of `Ω(P, P)` is
  the restriction to `𝔞_P` of an element of `Ω`. The statement uses
  `|Ω(P, P)|` as `Nat.card (weylParameterSet p l p l π)`, which needs no
  minimal parabolic; it is the sharper bound, and it implies Lapid's. Since
  `Nat.card` of an infinite set is `0`, finiteness of `Ω(P, P)` is part of
  the conclusion. This is explanatory and not proved here.
- Normalizations. Replacing `e` by `e ∘ T` (and `c j` by `c j ∘ T`, the same
  `φ`) multiplies `Θ` by `|det T|⁻¹` and both `dλ` and `(·,·)_P` by
  `|det T|⁻¹`, so both sides of the bound scale by `|det T|⁻²`. Lapid's
  measures are compatible, which is what `IsIwasawaCompatibleMeasure`
  expresses (Markdown of `AdelicInducedInnerProduct`). This is explanatory.
- Universe. `A^2_P` uses the canonical split component `A_M`, defined for
  `F : Type`.

## Scope

The integrability of the right-hand integrand of the inner product formula
is not asserted separately. Lapid's Proposition 1, Theorem 1 and Theorem 2
are not stated here; Proposition 6 is
`EisensteinImaginaryAxisHolomorphyStatement`.
