# Non-unitarizability of `ν^s ρ × ν^(-s) ρ` for large negative `s`

Author: Worker 1023.

`Langlands.Classification.TwoBlockLargeExponentNonUnitarizable.{uF,uV} F T` is a
proposition definition. It names the unbounded matrix coefficient step of the
reducibility sketch in Zelevinsky 1980, Proposition 1.11, proof, printed p.175
(PDF p.12). This module proves no theorem.

## Exact statement

Fix a prime `p`, a p-adic field `F : PadicField.{uF} p` and compatible
topological data `T : F.TopologicalData`; the statement works under
`T.topology`. For every `k : ℕ` with `hk : 0 < k`, every smooth representation
`ρ : SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier)` that is irreducible
(`ρ.representation.IsIrreducible`) and unitarizable
(`IsUnitarizable ρ.representation`), and every real `s < -(k : ℝ) / 2`, the
representation

```lean
(T.twistedProductInduced (Shahidi.twoBlocks k k hk hk)
  (twoBlockFactors hk hk ρ ρ) ![s, -s]).representation
```

is not unitarizable. This is the actual upper normalized product
`ν^s ρ × ν^(-s) ρ` on `GL_{2k}(F)`: `twistedProductInduced` applies the
Library's `normalizedProductInductionFunctor` of the standard two-block shape
`(k, k)` to the block family `(ν^s ρ, ν^(-s) ρ)`, where the first (upper-left)
block is `ρ` twisted by `T.determinantPowerCharacter k s` (that is
`ν^s = |det|^s`) and the second block is `ρ` twisted by `ν^(-s)`. Induction
uses positive half-modulus covariance and right translation.
`IsUnitarizable` is the Library notion: existence of a positive definite
invariant Hermitian form, with no topology or completion. The universes `uF`
and `uV` are independent.

## Provenance

This is a derived formulation of one assertion of Zelevinsky 1980 (literature
`zelevinsky-1980-induced-ii`), proof of Proposition 1.11, printed p.175 (PDF
p.12): "the matrix coefficients of `π_s` may be computed directly and one obtains
that for large `|s|` there exists a non-bounded matrix coefficient of `π_s`.
Therefore such `π_s` cannot be unitary." Zelevinsky's family is
`π_s = ν^{-s} ρ₀ × ν^{s} ρ₀` with unitary `ρ₀`; the family here is the same
with `s` replaced by `-s`, and the explicit threshold `s < -k/2` makes "large
`|s|`" precise for the negative half-line used by the intended application.
Irreducibility and unitarizability of `ρ` replace "cuspidal and unitary"; no
cuspidality is assumed.

## Proposed proof route (not part of the statement)

Let `a = diag(ϖ I_k, I_k)`. For a small compact open subgroup `K'` with an
Iwahori factorization `K' = N' M' N'^-` (upper unipotent part first) and a vector
`e` of `ρ ⊗ ρ` fixed by `M'`, let `f_e` be the induced function supported on
`P K'` with value `e` on `K'`. Since `a^{-n} N'^- a^n ⊆ N'^-` for `n ≥ 0`, the
functional `μ(f) = ℓ((average over K' of f)(1))` satisfies
`|μ(π(a^n) f_e)| = q^{-nk(k/2 + s)} |ℓ(e)|` (the central character of `ρ` has
modulus one by Schur's lemma and unitarity). This is unbounded for
`s < -k/2`. If `π` had an invariant positive form, the smooth functional `μ`
would be represented by a vector (`InvariantPositiveForm.toSmoothDual_surjective`,
using admissibility) and would be bounded on the orbit of `f_e` by the
Cauchy–Schwarz inequality. This paragraph describes an intended proof, not an
assumption.
