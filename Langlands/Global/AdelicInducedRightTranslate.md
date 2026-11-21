# Twisted right translation on adelic functions

`Langlands.Global.AdelicGroupPoints.IsIwasawaCompact.inducedRightTranslate`
is a function-level construction. For the supplied Iwasawa height `H_P`,
parameter `λ : X^*(P) ⊗ ℂ`, translating element `y`, and function `φ`, put

`T_{λ,y} φ(g) = exp(−⟨λ,H_P(g)⟩) · (parameterTwist φ λ)(g y)`.

Here `parameterTwist φ λ (g) = φ(g) exp(⟨λ,H_P(g)⟩)`, so the scalar
multiplying `φ(g y)` is `exp(⟨λ, H_P(g y) − H_P(g)⟩)`. This is in the
convention of Lapid, *On Arthur's asymptotic inner product formula of
truncated Eisenstein series* (2011), §2, p. 311: the half-modulus factor
is already built into the transformation law of the normalized inducing
function. In Arthur, *An introduction to the trace formula* (2005), §7,
pp. 32–34, the corresponding action on the inducing function in the
untwisted convention uses `λ + ρ_P` in the multiplier. The Library
construction directly conjugates right translation by its existing twist
from `AdelicEisensteinSeries`. The defining sum and integral use the
normalized formulas of Bernstein–Lapid, *On the meromorphic continuation
of Eisenstein series* (2024), §2.2, p. 191.

## Verified identities

- `parameterTwist_inducedRightTranslate`: retwisting `T_{λ,y} φ`
  cancels the factor at `g`, using `exp(−a) exp(a) = 1`, so the result is
  the translate `g ↦ (parameterTwist φ λ)(g y)`.
- `inducedRightTranslate_one` and `inducedRightTranslate_mul`: the
  identity acts trivially and `T_{λ,y} (T_{λ,z} φ) = T_{λ,y z} φ`.
  The latter uses the retwisting identity followed by associativity of
  adelic multiplication. `inducedRightTranslate_of_mem` uses right
  `K`-invariance of the height to cancel the twist for `y ∈ K`.
- `eisensteinSeries_inducedRightTranslate`: the retwisting identity turns
  each summand at `γ g` into the original summand at `γ (g y)`. Taking
  the unconditional sum gives the equality for the defining series.
- `intertwiningIntegral_inducedRightTranslate`: the same calculation
  at `w⁻¹ v g` gives pointwise equality of the two integrands, on the
  same quotient with the same measure. `intertwiningOperator_inducedRightTranslate`
  adds the target untwisting factor at `wλ`; on retwisting at `g y` the
  two opposite target height powers cancel. The operator on the source
  translate is thus the target translate by the same `y`, but with
  parameter `wλ`.

## Scope

The identities concern the actual totalized sum and integral in the
Library, and are proved by pointwise equality of summands and integrands.
They assert no convergence outside the regular chamber and no covariance
of meromorphic continuations. The construction does not assert that
translation preserves `A²_P` or archimedean `K`-finiteness, or that it
acts on `inducedHilbertSpace`. Those Hilbert-space and continuation
arguments, and the approximation by smooth compactly supported symmetric
families, are still needed for `WavePacketTranslationStatement`.
