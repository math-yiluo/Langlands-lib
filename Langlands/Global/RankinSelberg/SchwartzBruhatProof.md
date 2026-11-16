# Proof of the restricted-tensor description and Fourier inversion on `S(𝔸^n)`

This module proves `Langlands.Global.RankinSelbergGlobal.SchwartzBruhatStatement`. It contains
the basic facts about the adelic Schwartz–Bruhat space from J. R. Getz and H. Hahn, *An
Introduction to Automorphic Representations* (2024), §C.3, printed pp.553–554: the restricted
tensor product description on p.553, Lemma C.3.1, and the inversion formula (C.6) on p.554
(registered as `getz-hahn-2024-automorphic-representations`). Cogdell 2004, §2.3, printed
pp.208–209, uses these facts. The proof is the theorem

```
theorem Langlands.Global.RankinSelbergGlobal.SchwartzBruhatProof.schwartzBruhatStatement_proof :
    SchwartzBruhatStatement.{u}
```

## Proof

Fix a number field `F` with `CompactSpace (AdeleQuotient F)` and `n : ℕ`.

1. `schwartzBruhat F n = restrictedSchwartzBruhat F n` is `schwartzBruhat_eq_restricted`
   (module `SchwartzBruhatProof.PartA`). Locally constant compactly supported functions on
   `𝔸_f^n` are combinations of coset indicators of lattices `L_m^n`, which are restricted pure
   tensors. Conversely, finite parts of restricted pure tensors are locally constant with
   compact support.
2. For a standard `ψ` and `Φ ∈ schwartzBruhat F n`:
   - Integrability of `y ↦ Φ(y) ψ(Σ_j y_j x_j)` for `rectangleMeasure F 1 n` is
     `EqualAnalytic.integrable_mul_pairing`. It is applied to the integrability of `Φ`, which is
     the second component of `EqualAnalytic.schwartzBruhat_properties`. Both lemmas are in the
     Library: `|ψ| = 1`, and the integrand is a.e. strongly measurable.
   - `fourierTransform F n ψ Φ ∈ schwartzBruhat F n` and `Φ̂̂(x) = Φ(-x)` are
     `fourierTransform_mem_and_inversion` (module `SchwartzBruhatProof.Fourier`). There the
     transform of a pure tensor factors into an archimedean transform (`ArchFourier`) and a
     finite-adelic transform (`FiniteFourier`, `Duality`). Each satisfies inversion up to a
     constant. Poisson summation (`EqualAnalytic.hasSum_poisson`), applied to a nonnegative bump
     function times a lattice indicator and to its transform, shows that the total constant
     is `1`.

## Supporting modules

All in namespace `Langlands.Global.RankinSelbergGlobal.SchwartzBruhatProof`:

- `Langlands.Global.RankinSelberg.SchwartzBruhatProof.Lattice`: the lattices
  `L_m = ∏_v ϖ_v^(-m v) 𝒪_v ⊆ 𝔸_f` and `L_m^n`, coset indicators, and the expansion of locally
  constant compactly supported functions.
- `Langlands.Global.RankinSelberg.SchwartzBruhatProof.PartA`: clause 1.
- `Langlands.Global.RankinSelberg.SchwartzBruhatProof.ArchFourier`: Fourier inversion up to a
  constant for a symmetric nondegenerate pairing on a finite-dimensional real space.
- `Langlands.Global.RankinSelberg.SchwartzBruhatProof.Duality`: the annihilator of `L_m^n` under
  `ψ_f` is `L_(n_ψ - m)^n`.
- `Langlands.Global.RankinSelberg.SchwartzBruhatProof.FiniteFourier`: Fourier inversion up to
  `ν(L_m^n) ν(L_(n_ψ - m)^n)` for `L_m^n`-invariant compactly supported functions on `𝔸_f^n`.
- `Langlands.Global.RankinSelberg.SchwartzBruhatProof.Fourier`: the Fourier clauses.

The proof also uses the published `Langlands.Global.RankinSelberg.EqualAnalytic*` modules: the
factorization of the Fourier transform of pure tensors, Poisson summation, the domination and
integrability of Schwartz–Bruhat functions, and the description `ψ = ψ₀(b ·)` of standard
characters.

## Comparison with the source

Getz–Hahn prove Lemma C.3.1 by writing `f = f_S 1_((𝒪̂^S)^r)` for a large finite set `S` of
places and factoring the transform. The `S`-part is handled by the local theory, and the
unramified part is fixed by the transform (their Exercise C.5). They state (C.6) as the
existence of a unique self-dual Haar measure. The formal proof never identifies the local
self-dual measures.
It obtains inversion up to a constant at the archimedean places (by transport to Mathlib's
Euclidean Fourier transform) and at the finite adeles (by lattice duality). The product of the
constants is then fixed to be `1` by Poisson summation for the covolume-one measure. So the
Lean proof also shows that `rectangleMeasure F 1 n` is self-dual, as the statement's Markdown
explains via Tate's thesis.
