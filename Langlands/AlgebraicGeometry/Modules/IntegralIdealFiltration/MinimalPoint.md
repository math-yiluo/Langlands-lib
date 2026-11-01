# A minimal associated point of a quasi-coherent module

Author: Worker 716. This is an internal helper module for
`Langlands.AlgebraicGeometry.Modules.coherentIntegralIdealFiltration`. Its definition
`Good` is a derived device for the proof. The underlying algebra is the existence of
associated primes over noetherian rings (Mathlib).

## Results

- `exists_isPrime_annihilator`: let `W` be an open with noetherian `Γ(X, W)`, and let
  `t ≠ 0` in `Γ(Q, W)`. Then some multiple `b • t` has a prime annihilator `P`, that is,
  `c • (b • t) = 0 ↔ c ∈ P`. This applies Mathlib's
  `exists_le_isAssociatedPrime_of_isNoetherianRing` to the nonzero cyclic submodule
  `Γ(X, W) ∙ t`, so the witness of the associated prime is a multiple of `t`.
- `vanishingIdeal_closure_fromSpec`: let `p` be a point of `Spec Γ(X, V)` for an affine open
  `V`. On `V`, the vanishing ideal sheaf of the closure in `X` of `V.fromSpec p` is
  `p.asIdeal`. `fromSpec` is an open embedding, so the preimage of the closure is the
  closure of `{p}`, whose vanishing ideal is `p`.
- `fromSpec_mem_of_le`: if `p` contains the ideal of a closed set `Zc` on `V`, then the
  point `V.fromSpec p` lies in `Zc`.
- `Good Q Zc`: some affine open `V` carries a nonzero section of `Q` killed by
  `(vanishingIdeal Zc).ideal V`.
- `exists_good`: a nonzero affine section `t` gives a multiple `b • t` with prime
  annihilator `p`, and the closure of the point `p` is good.
- `closure_le_of_annihilator`: if moreover `t` is killed by the ideal of `Zc`, the closure
  of the point `p` lies in `Zc`.

## The minimal witness

`exists_minimal_witness` assumes `X` noetherian and `Q` quasi-coherent and nonzero. It
produces an affine open `U`, a section `s ∈ Γ(Q, U)` and a prime `p` of `Γ(X, U)` with
annihilator of `s` equal to `p`. For the closure `Zc` of the point `x = U.fromSpec p` it
also proves the torsion property. If a section `t` over an open `W` is killed by the
vanishing ideal of `Zc` and restricts to zero on every affine open inside `W ⊓ U`, then
`t = 0`.

Proof.

1. Since `Q ≠ 0`, it has a nonzero affine section, so good closed sets exist.
2. Closed sets of a noetherian space are well founded, so choose a minimal good `Zc`
   (`WellFounded.has_min`).
3. Its witness `t` gives a point `x` with `closure {x} ≤ Zc` and `closure {x}` good, so
   `closure {x} = Zc` by minimality. Take `U` and `s = b • t`.
4. For the torsion property, suppose `t|_V ≠ 0` on some affine `V ≤ W`. The same step gives
   a point `x'` of `V` whose closure is good and contained in `Zc`, hence equal to it. Since
   schemes are T0, `x' = x`, so `x` lies in `V ∩ U`.
5. A common basic open `D(f) = D(g)` of `V` and `U` around `x` (Mathlib's
   `exists_basicOpen_le_affine_inter`) is affine and lies in `W ⊓ U`. So the multiple of
   `t|_V` with annihilator the prime `p'` of `x'` vanishes on `D(f)`.
6. Quasi-coherence (`isLocalizingAt_of_isQuasicoherent`) gives `f ^ n ∈ p'`, so `f ∈ p'`.
   This contradicts `x' ∈ D(f)` (`fromSpec_preimage_basicOpen`).
