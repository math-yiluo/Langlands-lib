# Counting rational points in conjugates of compact sets by points of Siegel sets

Module `Langlands.Global.AdelicSiegelRationalConjugateCountingStatement` states
`Langlands.Global.SiegelRationalConjugateCountingStatement`. It does not prove it.

| Declaration | Kind | Source |
| --- | --- | --- |
| `SiegelRationalConjugateCountingStatement` | statement | derived: multiplicity refinement of the upper bound in Delorme 2023, Lemma 2.1 (i), with (2.9) |

## Statement

Let `F : Type` be a number field and `G` an affine group scheme over `F`, locally of finite type
and connected reductive (`IsConnectedReductive G`). The Siegel data are those of the module
`Langlands.Global.AdelicWavePacketRapidDecaySiegelReduction`, with the meaning given in its
Markdown page:

- an algebraic Siegel setup `(T, i, ν, T₀, j)` with `IsSiegelAlgebraicSetup F G T i ν T₀ j`;
- compact factors
  `C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅)`, whose
  compact subgroup is an arbitrary compact subgroup of `G(𝔸)`;
- a threshold `t : ℝ≥0ˣ` and a compact set `Ω ⊆ G(𝔸)`.

For every compact `E ⊆ G(𝔸)` there is `B ≥ 0` such that for every `a` in the intrinsic positive
torus `A_{T₀}` and every `x ∈ G(𝔸)` with `IsSiegelPoint F G T i ν T₀ j C t Ω a x`, the set

`P = G(F) ∩ x E x⁻¹`

is finite and `#P ≤ B · siegelModulus F G T i ν T₀ j a`. Here `G(F) = rationalSubgroup F G`,
`x E x⁻¹` is the image of `E` under `y ↦ x y x⁻¹`, and `#P` is `Set.ncard`.
`IsSiegelPoint … C t Ω a x` says `x = z · (n m a k) · w` with `z ∈ A_G`, `n ∈ Ω_N`, `m ∈ Ω_M`,
`a` in the weak simple-root chamber `|β(a)| ≥ t`, `k` in the compact subgroup of `C` and
`w ∈ Ω`. The modulus `siegelModulus a = ∏_{β ∈ Φ⁺} |β(a)|^{m_β} = δ_{P₀}(a) = e^{2ρ₀(H₀(a))}` is
the modulus of the standard minimal parabolic at the torus coordinate `a`, not at the full point
`x` (see the comparison below). The constant `B` depends on the setup, `C`, `t`, `Ω` and `E`, not
on `a` or `x`.

The Library's `AdelicRationalConjugateCountingAllPointsStatement` (Mœglin–Waldspurger I.2.4,
Lemma (a)(i)) bounds `#(G(F) ∩ x E x⁻¹)` by a power of the height of `x` at every point of
`G(𝔸)`. A fixed power of the height is in general not bounded by a multiple of `δ_{P₀}(a)` on a
Siegel set; the present statement is the bound by `δ_{P₀}(a)` itself.

## Sources

- P. Delorme, *On the spectral theorem of Langlands*, Adv. Math. 426 (2023) 109107, registered
  as `delorme-2023-spectral-theorem-langlands`; the published PDF in that folder has file SHA-256
  `9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`, and its numbering and page
  numbers are used here. §2, p. 7: Siegel domains (2.3) and (2.4), built with a good maximal
  compact subgroup `K₀` of `G(𝔸)`, with respect to which `H₀` is defined. §2, p. 8: (2.9), the
  function `Ξ^{[G]}(x) = vol_{[G]}(xY)^{-1/2}`, where `Y` is a fixed symmetric bounded
  neighbourhood of `1` in `G(𝔸)` (Delorme calls it `B`), and Lemma 2.1 (i),
  `Ξ^{[G]}(g) ∼ e^{ρ(H₀(g))}` on the Siegel domains `𝔰_G`, proved there by reference to
  Beuzart-Plessis–Chaudouard–Zydor, 2.4.2.3.

## Provenance (derived)

The statement is a multiplicity refinement of the upper bound `Ξ^{[G]}(x)² ≪ e^{2ρ₀(H₀(x))}` in
Delorme's Lemma 2.1 (i). Two points separate it from Delorme's formulation.

*Torus coordinate and full point.* At the torus coordinate the identity is exact:
`e^{2ρ₀(H₀(a))} = δ_{P₀}(a) = siegelModulus a`. At the full point it holds only up to constants.
Delorme's domains use the good maximal compact `K₀`, while `IsSiegelPoint` allows the arbitrary
compact subgroup `K` of `C` and an arbitrary compact suffix `Ω`. For `x = z · n m a k · w`,
`H₀(p g) = H₀(p) + H₀(g)` for `p ∈ P₀(𝔸)` gives
`H₀(x) = H₀(z) + H₀(m) + H₀(a) + H₀(k w)`. Pairing with `ρ₀` kills the split-central term
`H₀(z) ∈ 𝔞_G`, and `H₀` is bounded on the compact sets `Ω_M` and `K Ω`. Hence
`c₁ δ_{P₀}(a) ≤ e^{2ρ₀(H₀(x))} ≤ c₂ δ_{P₀}(a)` with `0 < c₁ ≤ c₂` depending on the setup, `C` and
`Ω`. The two sides differ in general. Take `G = SL₂` over `ℚ` with the upper triangular data,
`t = 1`, `a = 1`, all compact factors trivial except `Ω = {w}`, where `w` is `diag(2, 1/2)` at the
real place and `1` at the finite places. Then `x = w` is a Siegel point,
`e^{2ρ₀(H₀(w))} = 4` and `siegelModulus 1 = 1`.

*Count and quotient ball.* Let `Y` be a symmetric compact neighbourhood of `1` in `G(𝔸)`. If
`γ₁ y` and `γ₂ y` lie in `xY` for `γ₁, γ₂ ∈ G(F)`, then `γ₁ γ₂⁻¹ ∈ x Y Y⁻¹ x⁻¹`. Fixing one
point of a fibre of `xY → [G]`, the fibre therefore injects into `G(F) ∩ x Y Y⁻¹ x⁻¹`, so
`vol(Y) = vol(xY) ≤ #(G(F) ∩ x Y Y⁻¹ x⁻¹) · vol_{[G]}(xY)`: a lower bound for the quotient-ball
volume, and so an upper bound for `Ξ^{[G]}`. With `E = Y Y⁻¹` and the constant `B` of the
statement, `Ξ^{[G]}(x)² = vol_{[G]}(xY)⁻¹ ≤ B · δ_{P₀}(a) / vol(Y)` at the Siegel points `x`
with torus coordinate `a`. By the comparison above this is `≪ e^{2ρ₀(H₀(x))}`, the upper half of
Lemma 2.1 (i) on these families. The count, rather than the volume, is the form used to fold
local integrals onto `[G]` in `logSquareIntegrableSiegelDerivativeBounds_of_reduction` (module
`Langlands.Global.AdelicLogSquareIntegrableSiegelDerivativeReduction`).

The following route to the statement is explanatory and not proved here.

- *Packing.* Choose a compact neighbourhood `W` of `1` with `W W⁻¹ ∩ G(F) = {1}` (`G(F)` is
  discrete). The translates `γ W`, `γ ∈ P`, are disjoint and lie in `x E x⁻¹ W`, so
  `#P ≤ vol(x E x⁻¹ W) / vol(W) = vol(E · x⁻¹ W x) / vol(W)` by unimodularity.
- *Coordinates.* For `x = z p a k w` with `p = n m`, the central factor `z` cancels, and
  `x⁻¹ W x = (k w)⁻¹ a⁻¹ (p⁻¹ W p) a (k w)`, where `p`, `k`, `w` range over compact sets. The
  torus coordinate `a` is archimedean, so conjugation by `a` does not change the finite part of
  `p⁻¹ W p`. After shrinking `W`, the archimedean part of `p⁻¹ W p` lies in a product
  `W_U W_M W_U⁻` of small neighbourhoods in `U₀(F_∞)`, `M₀(F_∞)` and the opposite unipotent
  radical `U₀⁻(F_∞)` (open cell). Conjugation by `a⁻¹` keeps `a⁻¹ W_U a` in a fixed compact set on
  the chamber `|β(a)| ≥ t`, fixes `W_M`, and expands `U₀⁻(F_∞)` with Haar modulus `δ_{P₀}(a)`.
- *Volume.* For compact `D ⊆ G(𝔸)` and `E' ⊆ H = U₀⁻(F_∞)`, and a symmetric compact
  neighbourhood `V` of `1` in `H`, Tonelli's theorem and right invariance give
  `vol_G(D E') ≤ vol_G(D V) vol_H(V E') / vol_H(V)`. For `E' = a⁻¹ E₀ a`,
  `V E' = a⁻¹ ((a V a⁻¹) E₀) a` has `H`-volume at most `δ_{P₀}(a) vol_H(V' E₀)` for a fixed
  compact `V' ⊇ a V a⁻¹`, which gives `#P ≪ δ_{P₀}(a)`.
