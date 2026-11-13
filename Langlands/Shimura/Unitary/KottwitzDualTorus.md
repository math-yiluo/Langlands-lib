# The Frobenius action on the diagonal torus of the dual group

Module `Langlands.Shimura.Unitary.KottwitzDualTorus`, namespace
`Langlands.Shimura.KottwitzDual`.

This module is a supplement to items 3 and 5 of Task 5424. It imports only
`KottwitzPolynomial`.

The group `Ĝ = GL_1 × ∏_{τ ∈ S} GL_n` carries the action
`σ = dualAction S n L G` of a conjugation-compatible permutation
`G ∈ CMPerm S` (`KottwitzDualGroup`). `KottwitzPolynomial` writes points of the
diagonal torus `T̂` as `torusElement t`, `t = (ζ, (s_{τ,k}))`. It pairs them
with cocharacters in the free coordinates `a = (a₀, (a_{τ,k}))` by
`cocharPairing t a = ζ^{a₀} ∏_{τ,k} s_{τ,k}^{a_{τ,k}}`. It also defines the
norm `frobNorm G x f = x · σ(x) ⋯ σ^{f−1}(x)` on all of `Ĝ`.

This module proves that `σ` preserves `T̂` and computes it in the coordinates
`t`. It also computes the transpose of `σ` on cocharacters in the coordinates
`a`, and derives the same two formulas for the norm. The main results:

- `frobNorm G (torusElement t) f = torusElement (torusNorm G t f)`;
- `cocharPairing (torusNorm G t f) a = cocharPairing t (normCochar n G f a)`.

So the eigenvalue of `N_f(t̂)` on a weight `a` is the eigenvalue of `t̂` on the
explicit cocharacter `Σ_{r<f} (G^r)^* a`. The Harris comparison of item 5 uses
this to evaluate Kottwitz's polynomial on the weight lines of `r`. Worker 4811's
lift-independence supplement uses it as well.

## Provenance

The module contains no new mathematical notion. It computes the published
definitions `dualEndo`, `twist`, `torusElement`, `cocharPairing` and
`frobNorm` in coordinates. The resulting formulas are the coordinate form of
the Galois action on `T̂` derived in `KottwitzDualGroup.md` ("Derivation of
the dual group and of the Galois action"), following Borel (1979, §1.3, §2.3).
The formulas are proved in Lean, not quoted. Norms of torus elements and
pairings with Frobenius-averaged cocharacters are the standard description of
unramified parameters of tori (Borel 1979, §9.5) and of the weights of `r_μ`
under Frobenius (Kottwitz 1984, §2.3).

## Declarations

Throughout, `t : Lˣ × (S → Fin n → Lˣ)` and `a : ℤ × (S → Fin n → ℤ)`;
`rev k = n − 1 − k`; `base G` and `crosses G` are from `KottwitzDualGroup`.

### The pinned involution on the diagonal torus

- `det_diagUnit`: `det(diag s) = ∏_j s_j`.
- `signedAntidiagonal_mul_diagonal_mul_transpose`: `J' · diag(d) · J'ᵀ =
  diag(k ↦ d_{rev k})` for the signed antidiagonal `J'`.
- `twist_diagUnit`: the pinned involution `θ(g) = J' (g⁻¹)ᵀ J'⁻¹` sends
  `diag(s)` to `diag(k ↦ s_{rev k}⁻¹)`.
- `torusElement_one`: `torusElement 1 = 1`.

### The action on `T̂`

- `torusTwist G t` is the point `(ζ', s')` with
  - `ζ' = ζ · ∏_{τ : crosses G τ} ∏_j s_{τ,j}`;
  - `s'_{base G τ, k} = s_{τ, rev k}⁻¹` if `crosses G τ`, and
    `s'_{base G τ, k} = s_{τ,k}` otherwise.

  In Lean the second component is indexed by `τ'` with
  `τ = (base G)⁻¹ τ'`.
- `dualEndo_torusElement`: `dualEndo G (torusElement t) =
  torusElement (torusTwist G t)`. The `GL_1` coordinate uses `det_diagUnit`,
  and the crossing factors use `twist_diagUnit`.

### The transpose on cocharacters

- `cocharPullback n G` is the additive endomorphism
  `a ↦ (a₀, (τ, k) ↦ if crosses G τ then a₀ − a_{base G τ, rev k} else
  a_{base G τ, k})` (`cocharPullback_apply`).

  Interpretation: extend `a` to all complex embeddings `i` of `K` by
  `a_{Φτ,k} = a_{τ,k}` and `a_{conj(Φτ),k} = a₀ − a_{τ, rev k}`, as in
  `X_*(T)` of `KottwitzDualGroup.md`. Then `G^* a` is `i ↦ a_{G i}`. For the
  Frobenius permutation `G` (`i ↦ σ ∘ i`) this is the action of `σ^{-1}` on
  `X_*(T)`, which matches `(σ t̂)(λ) = t̂(σ^{-1} λ)`.
- `cocharPullback_one`, `cocharPullback_mul`
  (`(G H)^* a = H^* (G^* a)`), and `cocharPullback_pow`
  (`(G^r)^* = (G^*)^[r]`).
- `cocharPairing_add`, `cocharPairing_zero`, `cocharPairing_one`,
  `cocharPairing_sum`, `cocharPairing_prod`: the pairing is multiplicative in
  each argument. Multiplicativity in `t` (`cocharPairing_mul`) is in
  `KottwitzPolynomial`.
- `cocharPairing_torusTwist`: `cocharPairing (torusTwist G t) a =
  cocharPairing t (cocharPullback n G a)`. At a crossing the exponent of
  `s_{τ,k}` is `a₀ − a_{base G τ, rev k}`. Here `a₀` comes from the `GL_1`
  coordinate, and the reindexing `k ↦ rev k` comes from `θ`.

### The norm

- `torusNorm G t f = ∏_{r < f} torusTwist (G ^ r) t`.
- `normCochar n G f a = Σ_{r < f} cocharPullback n (G ^ r) a`. By
  `cocharPullback_pow`, this is `Σ_{r<f} (G^*)^[r] a`.
- `frobNorm_torusElement`: `frobNorm G (torusElement t) f =
  torusElement (torusNorm G t f)`. The proof is by induction on `f`, using
  `(dualAction G)^r = dualAction (G^r)` and `torusElement_mul`.
- `cocharPairing_torusNorm`: `cocharPairing (torusNorm G t f) a =
  cocharPairing t (normCochar n G f a)`.

## Scope

- Only the diagonal torus is treated. The action on the whole of `Ĝ` is
  `dualEndo` from `KottwitzDualGroup`.
- No statement here involves a prime, a place, or the Frobenius permutation
  `frobeniusCMPerm`. All results hold for every `G ∈ CMPerm S` and every
  field `L`.

## Sources

- A. Borel, *Automorphic L-functions*, Corvallis Part II (1979)
  (`borel-1979-automorphic-l-functions`): §1.3 and §2.3, printed pp.29-31,
  for the action `μ_G` and the L-group built from it; §9.5, printed pp.42-43,
  for unramified characters of tori and their parameters `t ⋊ Fr`.
- R. E. Kottwitz, *Shimura varieties and twisted orbital integrals*, Math.
  Ann. 269 (1984), §2.3, printed pp.295-296
  (`kottwitz-1984-shimura-varieties-twisted-orbital-integrals`): the weights
  `ν` of `r_μ` restricted to `T̂` and the action of Frobenius on them.
