# Smooth wave packets, the inner product on `A^2_P`, and Levi data

Module `Langlands.Global.AdelicLocalWavePacketStatement` states the five
premises from which `Langlands.Global.BoundedWavePacketReduction` derives
Lapid's Lemma 10 (`BoundedWavePacketStatement`):

- `Langlands.Global.LocalWavePacketInnerProductStatement`: Lapid's
  Proposition 2 for wave packets in Lapid's space `W_P`, that is, with smooth
  coefficients supported where the Eisenstein series are regular;
- `Langlands.Global.LocalWavePacketNormBoundStatement`: the bound (19) of
  Lemma 10 for the same wave packets;
- `Langlands.Global.InducedInnerProductSesquilinearStatement`: `(·,·)_P` is
  sesquilinear on finite linear combinations of elements of `A^2_P`;
- `Langlands.Global.LeviProjectionExistenceStatement`: a parabolic `P = MU`
  has a Levi projection `π : P → M` with `l ≫ π = 𝟙`;
- `Langlands.Global.WavePacketIwasawaCompatibleMeasureExistenceStatement`: `M(𝔸)` has
  a Haar measure compatible with the Iwasawa decomposition.

None of them is proved here. The module proves one consistency theorem,
`Langlands.Global.wavePacketInnerProduct_of_local`:
`LocalWavePacketInnerProductStatement` implies the published
`WavePacketInnerProductStatement`.

## Sources

- E. Lapid, *On Arthur's asymptotic inner product formula of truncated
  Eisenstein series*, in: On Certain L-Functions, Clay Math. Proc. 13 (2011),
  pp. 309–331, registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein` (volume PDF; PDF
  page = printed page + 9).
  - §2, p.311: `A^2_P` and the inner product `(·,·)_P`.
  - §3, p.314: "denote by `W_P` the space of compactly supported smooth
    functions on `i𝔞_P^*` taking values in a finite-dimensional subspace of
    `A^2_P` such that `E_P(·, φ(λ), λ)` is smooth on `i𝔞_P^*`", the norm (3)
    and Proposition 2: "For any `φ ∈ W_P`, `Θ_{P,φ} ∈ L²(G \ G(𝔸))`. The
    inner product is given by (4) for any `φ' ∈ W_{P'}`."
  - §8, Lemma 10, p.329, with the bound (19)
    `‖Θ_φ‖²_{L²(G \ G(𝔸))} ≤ |Ω| ‖φ‖²_*`, and its proof, which uses (4) and
    (19) for the smooth approximations `φ_n ∈ W_P`.
- J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations*,
  GTM 300 (2024), registered as `getz-hahn-2024-automorphic-representations`:
  - Theorem 1.5.8, Definition 1.5.9 and the remark after it, p.16: an affine
    group `G` over a field of characteristic zero is `M R_u(G)` for a
    subgroup `M`; a Levi subgroup `M` maps isomorphically onto `G/R_u(G)`;
    and if `N_k̄ = R_u(G_k̄)` then `G = MN` is a semidirect product;
  - Exercise 3.5, p.99: if `G(𝔸_F) = P(𝔸_F)K`, the Haar measures on
    `G(𝔸_F)`, `P(𝔸_F)` and `K` can be normalized so that `dg = dp dk`.

## Statements

### `LocalWavePacketInnerProductStatement`

The data and conclusion of `BoundedWavePacketInnerProductStatement` (see the
Markdown of `AdelicBoundedWavePacketStatement`), with one change: each
coefficient `c j` is smooth (`ContDiff ℝ (⊤ : ℕ∞)`) and zero outside the
compact set `S`, instead of measurable, bounded and zero outside `S`, and the
same for `c' j` and `S'`. As in that statement, the continuations `E j` are
meromorphic with a domain of holomorphy `D ⊇ {i e(x) | x ∈ S}`, the
intertwining coefficients `coeff t j i` with a domain `DM ⊇ {i e(x) | x ∈ S}`,
and `E' j` with `D' ⊇ {i e'(x') | x' ∈ S'}`. The conclusion: `y ↦ Θ(y.out)`
and `y ↦ Θ'(y.out)` are in `L²(G(F) \ G(𝔸), μG)` and
`∫ Θ(y.out) · conj Θ'(y.out) dμG(y)` is the right side of (4) written in the
data.

Correspondence: `φ(λ) = ∑ j, c j x · v j` at `λ = i e(x)` is smooth and
compactly supported with values in the span of the `v j`. Near every point of
`S`, every `E(v j, ·)` is holomorphic, because `D` is the open domain of
holomorphy of the continuations; outside `S` the function `φ` is `0`. So
`λ ↦ E_P(·, φ(λ), λ)` is smooth on `i𝔞_P^*` and `φ ∈ W_P`. Lapid's `W_P`
also allows poles of single `E(v j, ·)` near the support that cancel in
`E(φ(λ), λ)`; such `φ` are not covered, so the statement claims at most
Proposition 2. It is the case of smooth coefficients of
`BoundedWavePacketInnerProductStatement`; this is proved as
`localWavePacketInnerProduct_of_bounded` in `BoundedWavePacketReduction`.

### `LocalWavePacketNormBoundStatement`

The data and conclusion of `BoundedWavePacketNormBoundStatement`, with each
`c j` smooth and zero outside the compact `S` instead of measurable, bounded
and zero outside `S`. The conclusion: `weylParameterSet p l p l π`
(`Ω(P, P)`) is finite, `y ↦ Θ(y.out)` is in `L²(μG)`, and
`∫ ‖Θ(y.out)‖² dμG ≤ |Ω(P, P)| · ∫ Re (φ(x), φ(x))_P d(spectralMeasure n)(x)`
with `φ(x) = ∑ j, c j x · v j`.

Correspondence: this is (19) for `φ ∈ W_P` (as above), with the constant
`|Ω(P, P)|` of `BoundedWavePacketNormBoundStatement`, whose Markdown explains
why it is the sharper form of Lapid's `|Ω|`. For `φ ∈ W_P` it follows from
(4) with `φ' = φ`, the unitarity of `M(s, λ)` on `i𝔞_P^*` and the invariance
of `dλ` under `Ω(P, P)`. This is the step of Lapid's proof of Lemma 10
("by (4), `Θ_{φ_n}` is a Cauchy sequence") applied to `φ_n - φ_m`. It is the
case of smooth coefficients of `BoundedWavePacketNormBoundStatement`
(`localWavePacketNormBound_of_bounded`).

### `InducedInnerProductSesquilinearStatement`

The data: the parabolic setting of `BoundedWavePacketNormBoundStatement`
(`G` connected reductive, `P = MU` with presentation `r` and geometric
unipotent radical `iU`, a Levi projection `π : P → M` with `l ≫ π = 𝟙`), a
maximal compact `K` with
`P(𝔸)K = G(𝔸)`, a closed matrix embedding `rho`, the smooth-structure data,
a Haar measure `μM` on `M(𝔸)` with `IsIwasawaCompatibleMeasure`, coordinates
`e`, a continuous compactly supported weight `β` with `∫ β = 1`, and
`v j ∈ A^2_P` (`IsSquareIntegrableInducedForm`) for `j : Fin k`. The
conclusion: for all `z z' : Fin k → ℂ`,
`inducedInnerProduct K hK.isCompact p l μM e β (∑ j, z j · v j) (∑ j, z' j · v j)`
equals `∑ j, ∑ j', z j · conj (z' j') · inducedInnerProduct … (v j) (v j')`.

Provenance (derived): Lapid's `(·,·)_P` is the inner product of the
pre-Hilbert space `A^2_P` (§2). The Library's `inducedInnerProduct` writes it
in Iwasawa coordinates as `∫_K ∫_{M(F) \ M(𝔸)} β(y(m)) δ_P(m)⁻¹ φ(mk) conj ψ(mk)`
(Markdown of `AdelicInducedInnerProduct`). For `φ, ψ ∈ A^2_P` this double
integral converges absolutely: by the `A^n_P` condition
`δ_P(am)⁻¹ |φ(amk)|² = δ_P(m)⁻¹ |φ(mk)|²` for `a ∈ A_M`, so integrating
`|β(y(am))|` over `A_M` leaves `‖β‖₁` times the square integral of `φ` on
`K × A_M M(F) \ M(𝔸)`, which is finite; Cauchy–Schwarz bounds the mixed
terms. Linearity of absolutely convergent integrals then gives the
expansion. The integral of `|β(y(a))|` over `A_M` is finite because
`a ↦ y(a)` (the coordinates of `H_P(a)`) is proper on `A_M`. This uses that
the restriction `X^*(P) → X^*(M)` along `l` is surjective, which `π` gives:
`χ ↦ χ ∘ π` is a section. The hypothesis on `π` is therefore part of the
statement, as in `LocalWavePacketNormBoundStatement`; such a `π` exists by
`LeviProjectionExistenceStatement`. The statement records this property of the formalization, which
the reduction needs to control `‖φ(x)‖²_P` by the coefficients.

### `LeviProjectionExistenceStatement`

The data: the parabolic setting (`G` connected reductive, `P = MU` with
presentation `r`, `iU` a geometric unipotent radical). The conclusion: there
is a group scheme homomorphism `π : P ⟶ M` with `l ≫ π = 𝟙 M`.

Correspondence: by Getz–Hahn, p.16 (Definition 1.5.9 and the remark after
it), `P` is the semidirect product of its Levi subgroup `M` and its unipotent
radical `U`, and `M → P/U` is an isomorphism; `π` is the quotient map
`P → P/U` followed by the inverse of this isomorphism. The target statement asks for `π` only for
the second parabolic; the reduction uses this statement to obtain one for the
first.

### `WavePacketIwasawaCompatibleMeasureExistenceStatement`

The data: the parabolic setting and a maximal compact `K` with
`P(𝔸)K = G(𝔸)`. The conclusion: there is a Haar measure `μM` on `M(𝔸)` with
`IsIwasawaCompatibleMeasure K hK.isCompact p iU l μM`, that is,
`∫_G f = ∫_K ∫_M ∫_U δ_P(m)⁻¹ f(u m k) du dμ_M(m) dk` for every compactly
supported continuous `f`, with Mathlib's Haar measure on `G(𝔸)`,
`vol(U(F) \ U(𝔸)) = 1` and `vol(K) = 1`.

Correspondence: Getz–Hahn, Exercise 3.5, gives `dg = dp dk` for suitable
normalizations; on `P(𝔸) = U(𝔸) M(𝔸)` the left Haar measure is
`δ_P(m)⁻¹ du dm` in the coordinates `p = um`, since conjugation by `m`
scales `du` by `δ_P(m)`. Fixing `dg`, `du` and `dk` as in the definition
determines the Haar measure `dm = μ_M`.

## The theorem `wavePacketInnerProduct_of_local`

Given `LocalWavePacketInnerProductStatement`, the data of
`WavePacketInnerProductStatement` (smooth compactly supported `c j`, domains
`D`, `D'`, `DM` containing all of `i𝔞_P^*` or `i𝔞_{P'}^*`) are those of the
local statement with `S = ⋃ j, tsupport (c j)` (compact as a finite union of
compact sets; each `c j` vanishes outside its topological support) and
`S' = ⋃ j, tsupport (c' j)`; the image conditions hold because the domains
contain the whole range of `imaginaryParameter`. So a proof of the local
statement also proves the published Proposition 2.
