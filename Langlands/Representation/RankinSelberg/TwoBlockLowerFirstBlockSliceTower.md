# The first-block slice tower of the lower mixed quotient

Module `Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockSliceTower`.
Statement `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.FirstBlockSliceTowerStatement`,
proved by `firstBlockSliceTower`.
Authors: Worker 1179.

This module proves the geometric measure identity behind JPSS (1983),
Section 4.9, equation (8), printed page 418, one determinant slice at a time,
for the actual first-block kernel of the published lower mixed quotient data.
It imports the helper module `TwoBlockLowerFirstBlockUnipotentCoordinates`.

## Setting

Fix a prime `p`, a canonical `F : PadicField.{uF} p` (canonical topology,
valuation, local-field structure, Borel measurable structures on the field,
the groups and the quotients), and a two-block shape
`h : ∑ i, (m i + 1) = t + 1`. Put `a = m 0 + 1`, `b = m 1 + 1`,
`G = GL_{t+1}(F)`, and `q = F.canonicalTopologicalData.residueCardinality`.
The objects are the published ones:

| Symbol | Lean object |
| --- | --- |
| `H⁻`, `lowerHaar` | `lowerBlockUnipotent h F.Carrier` and its prescribed Haar `lowerHaar F h` |
| `L⁻`, `lowerMixedHaar` | `lowerMixedSubgroup F h` and its fixed Haar `lowerMixedHaar F h` |
| `HQ = H⁻ \ G` | `LowerQuotient h F.Carrier` |
| `LQ = L⁻ \ G` | `LowerMixedQuotient F h` |
| `AQ = N_a \ GL_a` | `LeftUnipotentQuotient (m 0) F.Carrier` |
| `LQ0`, `HQk` | `TwoBlockLowerFirstBlockQuotient.determinantSlice F h 0`, `TwoBlockLowerUnipotentQuotient.determinantSlice F h k` |
| `κ_k` | `firstBlockKernel F h νA hInv k`, the actual first-block kernel `[g] ↦` pushforward of `νA` restricted to the small slice `k` under `[v] ↦ [I(v) g]` |
| `I(v)` | `firstBlockEmbedding h F.Carrier v = diag(v, 1)` |

## Statement

`FirstBlockSliceTowerStatement F h` is the proposition: for every measure
`νA` on `AQ` that is s-finite, invariant under right translation by
`GL_a^0` (`NormOneRightInvariant`), and compatible with
`generalLinearHaar F.Carrier (m 0)` and `unipotentHaar F.Carrier (m 0)`; for
every measure `νL` on `LQ` compatible with `generalLinearHaar F.Carrier t` and
`lowerMixedHaar F h`; for every measure `νMinus` on `HQ` compatible with
`generalLinearHaar F.Carrier t` and `lowerHaar F h`; and for every integer `k`,

`ENNReal.ofReal (q ^ (-(k * b))) • (κ_k ∘ₘ νL.restrict LQ0) = νMinus.restrict HQk`.

Here `IsCompatible H μG μH ν` is the published compatibility structure: `ν`
is nonzero, regular and right-translation invariant, and for every compactly
supported continuous complex `f` on the ambient group the `μH` average
`[x] ↦ ∫_H f(h x) dμH` is `ν`-integrable with
`∫_{H\G} (∫_H f(h x) dμH) dν = ∫_G f dμG`. The density `q^(-k b)` equals
`|det v|^b` for `v` in the small slice `k`. Theorem `firstBlockSliceTower`
proves the proposition from `firstBlockKernel_comp_zeroSlice`, which is the
same identity with the hypotheses as arguments.

## Supporting results

- `leviEmbedding_mul_lowerRadical_mul_firstBlockEmbedding`:
  `diag(u, y) R(Z) I(v) = diag(u v, y) R(Z v)`; and
  `firstBlockEmbedding_mul_leviEmbedding`: `I(z) diag(u, y) = diag(z u, y)`.
- `ambientSlice F n k = {g ∈ GL_n | ord(det g) = k}`, an internal definition
  of the ambient determinant slice; `isClopen_ambientSlice`;
  `ord_determinant_mul_of_mem` (left multiplication by `GL_n^0` keeps the
  order); `quotientAverageReal_indicator_ambientSlice` (averaging over a
  subgroup of `GL_n^0` commutes with multiplying by the indicator of
  `ambientSlice F n k`).
- `lintegral_mul_right_of_ord`: for every additive Haar `μR` on `b × a`
  matrices and `ord(det v) = k`,
  `q^(-k b) ∫ φ(Z v) dμR = ∫ φ dμR`.
- `small_orbitKernel_comp_slice`: for `νA` compatible as above and any `z`
  with `ord(det z) = k`, the `N_a`-orbit kernel composed with `νA` restricted
  to the small slice `k` is the pushforward of `normOneHaar` under `u ↦ z u`.
- `lintegral_firstBlockFiberPoint_quotientAverageReal` (per point): for
  nonnegative `f ∈ C_c(G)` and `ord(det z) = k`, `q^(-k b)` times the
  `νA|slice k` integral of the `H⁻` averages of `f` at the fiber points
  `[I(v) g]` equals the `L⁻` average at `[g]` of `x ↦ f(I(z) x)`.
- `lintegral_firstBlockKernel_comp_quotientAverageReal`: the same identity
  integrated against an arbitrary measure `ν` on `LQ` through `κ_k`.
- `eq_of_lintegral_lowerQuotientAverageReal`: two measures on `HQ` that give
  the same finite value on every `H⁻` average of a nonnegative `f ∈ C_c(G)`
  are equal.

## Proof

1. *Per-point identity.* At a fiber point `[I(v) g]` with `ord(det v) = k`,
   the `H⁻` average is written in block coordinates with
   `lintegral_lowerHaar` (helper module), using the arbitrary rectangular Haar
   `μR`. The algebra identity moves `I(v)` through `diag(x, y) R(Z)`, and
   `lintegral_mul_right_of_ord` absorbs the density into the change
   `Z ↦ Z v`; Tonelli then exchanges the `N_a` and `N_b` integrals. The
   result is the integral over `x ∈ N_a` of a fixed function `Φ` at `x v`.
   Integrating over `νA|slice k` turns the `N_a`-integral and the `νA`-integral
   into the orbit kernel composed with `νA|slice k`
   (`Measure.lintegral_bind`, `orbitKernel_mk`). By
   `small_orbitKernel_comp_slice` this is the integral of `Φ(z u)` over
   `u ∈ GL_a^0`. Using `I(z) diag(u, y) = diag(z u, y)`, Tonelli and the
   published `lintegral_mixedHaar_radical`, this equals `c(μR)` times the `L⁻`
   average of `x ↦ f(I(z) x)` at `[g]`; the published cube mass bounds
   `0 < c(μR) < ∞` cancel the common factor.
2. *Integration.* The per-point identity is integrated against `ν` with
   `Measure.lintegral_bind` and the published representative law
   `firstBlockKernel_mk`, with `μR = Measure.addHaar`.
3. *Both sides integrate to the same value.* Fix `z` with `ord(det z) = k`
   (`exists_determinantOrder`). For nonnegative `f ∈ C_c(G)`, the kernel
   side equals `∫_{LQ0}` of the `L⁻` averages of `f(I(z) ·)`; since
   `L⁻ ⊆ GL^0`, cutting by `LQ0` is averaging the function cut by
   `ambientSlice 0`, so compatibility of `νL`
   (`RecursiveIntegration.lintegral_quotientAverageReal`) and left invariance
   of the Haar of `G` under `I(z)` give `∫_G 1_{G^k} f`. On the other side,
   `H⁻ ⊆ GL^0` and compatibility of `νMinus` give the same value
   `∫_G 1_{G^k} f`, which is finite.
4. *Extension.* `eq_of_lintegral_lowerQuotientAverageReal` concludes. Its
   proof lifts each nonnegative compactly supported continuous function on
   `HQ` to a nonnegative `f ∈ C_c(G)` with that average
   (`realQuotientPositiveLifting`), deduces finiteness on compact sets from an
   Urysohn function, and applies uniqueness of regular measures with equal
   integrals of compactly supported continuous functions
   (`Measure.ext_of_integral_eq_on_compactlySupported_nnreal`).

The proof works directly on each slice `k` with the left coset `z GL_a^0`;
no modulus of conjugation by `L⁻` is used.

## Provenance

Equation (8) of JPSS (1983), Section 4.9, printed page 418, reads
`∫_{H_{t₁,t₂} \ G_r} F(g) dg = ∫_{L \ G_r^0} dh ∫_{N_{t₁} \ G_{t₁}}
F[diag(a, 1) h] |det a|^{t₂} d^× a`. The statement here is a derived
measure-theoretic form of that formula restricted to the small determinant
slice `k`, where `|det a|^{t₂} = q^(-k b)`: the inner integral is the actual
first-block kernel, the outer measure is `νL` restricted to `LQ0`, and the
left side is `νMinus` restricted to the slice `HQk`. The compatibility
hypotheses fix the normalizations; JPSS does not state them. The kernel
formulation, slice decomposition and regular-measure uniqueness argument are
internal precision and are not claimed to appear in the source. Summing over
`k` and the analytic consequences (Tonelli, integrability) are not part of
this module.
