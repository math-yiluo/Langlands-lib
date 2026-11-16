# Fourier analysis of coset indicators on a totally disconnected group

Module `Langlands.Global.RankinSelberg.SchwartzBruhatProof.FiniteFourier`, namespace
`Langlands.Global.RankinSelbergGlobal.SchwartzBruhatProof`. It is a supporting module for
the proof of `Langlands.Global.RankinSelbergGlobal.SchwartzBruhatStatement`. It supplies the
finite-adelic half of the Fourier inversion argument.

## Provenance

These are internal lemmas. They contain the standard computation of the Fourier transform of the
indicator of a coset of a compact open subgroup: it is the volume times a character times the
indicator of the annihilator. Iterating this gives Fourier inversion on locally constant
compactly supported functions, up to the constant `ν(H) ν(H')`. This is the finite-adelic input
of Getz–Hahn, *An Introduction to Automorphic Representations* (2024), Lemma C.3.1 and (C.6),
printed p.554. The constant is pinned down globally in module `Fourier`. The proofs are written
for this formalization.

## Generic part

`G` is a commutative topological additive group with Borel measurable structure, and `ν` is a
left-invariant measure on it.

- `IsFinitePairing p` for `p : G → G → ℂ`: `p` is additive-to-multiplicative in the first
  variable, symmetric, of norm one, continuous in the first variable and locally constant in the
  second. Consequences: `add_right`, `ne_zero` and `zero_left` (`p(0, η) = 1`).
- `isLocallyConstant_finset_sum`: finite sums of locally constant functions are locally constant.
- `finFourier ν p f η = ∫ f(u) p(u, η) dν(u)`.
- `integral_cosetIndicator_mul_eq`: `∫ 1_(a+H)(u) p(u, η) dν = p(a, η) ∫_H p(w, η) dν(w)`, by
  translation invariance.
- `integral_cosetIndicator_mul_of_forall`: if `p(·, η)` is trivial on an open `H`, the integral is
  `ν(H) p(a, η)`.
- `integral_cosetIndicator_mul_of_exists`: if `p(h₀, η) ≠ 1` for some `h₀ ∈ H`, the integral is
  `0`. Translating by `h₀` multiplies it by `p(h₀, η)`.
- `finFourier_cosetIndicator`: suppose `H` is open and `H'` is the annihilator
  `{η | p(h, η) = 1 for all h ∈ H}`. Then `F(1_(a+H)) = ν(H) p(a, ·) 1_(H')`.
- `integrable_cosetIndicator_mul`: for compact open `H` and `ν` finite on compacts, the integrand
  is integrable.
- `finFourier_finFourier` (**finite Fourier inversion**): let `H, H'` be compact open, each the
  annihilator of the other, and let `f` be compactly supported and `H`-invariant. Then `F f` is
  locally constant with compact support, and `F F f(x) = ν(H) ν(H') f(-x)`. Proof: expand
  `f = Σ_(a ∈ s) f(a) 1_(a+H)` (`exists_eq_sum_cosetIndicator`). Then
  `F f = Σ_a f(a) ν(H) p(a, ·) 1_(H')` is locally constant and supported in `H'`. Transforming
  once more, `∫_(H') p(η, a + x) dν(η) = ν(H') 1_(a+H)(-x)` by the annihilator property
  `hann'`. Summing gives `ν(H) ν(H') f(-x)`.

## The finite adeles

- Local instances `finiteFourierMeasurableSpace` (the Borel σ-algebra on `𝔸_f`),
  `finiteFourierBorelSpace`, `finiteFourierSecondCountable` and `finiteFourierLocallyCompact`
  (from the Library's `finiteAdeles_secondCountableTopology` and
  `finiteAdeles_locallyCompactSpace`). These are the measurability data under which the
  Library's `EqualAnalytic` modules state the finite part of the Fourier transform. They are
  `local`, so they are visible only where a module activates them.
- `rowPairing ψ n u η = ψ_f(Σ_j u_j η_j)` on `𝔸_f^n`, and `isFinitePairing_rowPairing`. Local
  constancy in `η` comes from `isLocallyConstant_finiteCharacter` (module `Duality`).
- `finiteFourier_inversion`: for `f` compactly supported and `L_m^n`-invariant, the transform
  `finFourier addHaar (rowPairing ψ n) f` is locally constant with compact support. Also
  `F F f(x) = ν(L_m^n) ν(L_(n_ψ - m)^n) f(-x)`, where `ν = Measure.addHaar` on `𝔸_f^n`. This
  is `finFourier_finFourier` with `H = L_m^n` and `H' = L_(n_ψ - m)^n`. The two annihilator
  conditions are `forall_finiteCharacter_sum_eq_one_iff` (module `Duality`) for `m` and for
  `n_ψ - m`, using `n_ψ - (n_ψ - m) = m`.
