# The block-pair gamma law as a local rational-function identity

Author: Worker 1695.

This module turns the block-pair gamma law of Henniart 2002, §2.4 (the
published, unproved statement `LocalFactor.PairBlock.BlockPairGamma F`) into an
identity of rational functions at the local level. It also computes the epsilon
value of a pair of bottom-field blocks from those of its twisted factors. Only
the standard axioms are used.

Throughout, `F : PadicField.{uF} p`, `ω = (localNormCharacter F).toMonoidHom`,
`q = F.canonicalTopologicalData.residueCardinality` and
`δ = residueReflection F = q⁻¹`. `B`, `B'` are local Weil representations with
carrier in `uP`, and `ρ = baseLift F B`, `ρ' = baseLift F B'` are their lifted
restrictions to the bottom field `⊥` (module `BaseLocalEuler`). `LR(A)` denotes
`WeilDeligne.rationalLRatio A (localInertia F) (localGeometricFrobenius F) δ`,
that is `P_A(X) / P_(A^∨)(δ/X)`.

## Abbreviations

- `localBlockTensor F B B' a b`: the local pair
  `T = block ω B (a+1) ⊗ block ω B' (b+1)` (blocks `B ⊗ Sp(a+1)`, `B' ⊗ Sp(b+1)`).
- `localTwistTensor F B B' k`: the local pair `L_k = zm(ω^k B) ⊗ zm(B')`, both
  factors with zero monodromy.
- `baseBlockTensor F B B' a b`: the bottom-field pair
  `block ρ (a+1) ⊗ block ρ' (b+1)`.
- `restrictBlockTensorBaseEquiv`: the restriction of `T` to `⊥` is equivalent to
  `baseBlockTensor`.
- `baseSpectralParameter_eq`, `baseSpectralParameter_one_sub`: over `⊥`, the
  spectral variable at `s` is the local spectral point `q^(-s)`, and at `1 - s`
  it is `δ / q^(-s)`.

## Main results

- `rationalLRatio_localBlockTensor`: assume `hBPG : BlockPairGamma F`, a system
  `(eC, ε, hε)`, a character `ψ'`, a Haar measure `μ` over `⊥`, continuous `B`,
  `B'`, and a geometric Frobenius `Φ` over `⊥`. Let `c` be the
  `quotientConstantCorrection` and `d` the `conductorCorrection` of
  `baseBlockTensor` at `Φ`. Then in `RatFunc ℂ`

  `C(c) · X^d · LR(T) = ∏_(i ≤ a) ∏_(j ≤ b) LR(L_(i+j))`.

  Proof. The published consequence `quotientValue_mul_lRatioValue_block` of
  `BlockPairGamma` (module `BlockPairEpsilon`) gives, at every common regular
  point `s`,
  `quotientValue(s) · lRatioValue_T(s) = ∏ lRatioValue_(i+j)(s)` over `⊥`. The
  bottom-field Euler polynomials of `baseBlockTensor`, of the twisted factors of
  `ρ ⊗ ρ'` and of their duals are the local ones of `T` and `L_(i+j)`
  (`eulerPolynomial_base_of_equiv` and its dual). The bottom-field spectral
  variables are `x = q^(-s)` and `δ / x`. So both sides, evaluated at `x`, agree
  for all `x` in the infinite set `U` of spectral points `q^(-s)`, `s > 0` real,
  minus two finite sets: the roots of `P_T ∏ P_(L_(i+j))`, and `δ / y` for `y` a
  root of `P_(T^∨) ∏ P_(L_(i+j)^∨)`. The evaluation lemmas of
  `SegmentEpsilonAlgebra` and `rationalFunction_eq_of_infinite_eval_eq` finish
  the proof.
- `conditionalPairEpsilonValue_baseBlock`: fix a system, `ψ'`, `μ`, `Φ`, `s` and
  data `e i j = (c_ij, m_ij)`. Suppose the epsilon value of each pair
  `(twistedFactor ρ (i+j), twistedFactor ρ' 0)` at `s` is `c_ij q^(-m_ij s)`.
  Then the epsilon value of `(block ρ (a+1), block ρ' (b+1))` at `s` is

  `epsilonMonomial q ((∏ c_ij) · c) ((Σ m_ij) + d) s`,

  with `c`, `d` the quotient correction data at `Φ` as above. The proof uses the
  published results of `BlockPairEpsilon`:
  - GA1 `conditionalPairEpsilonValue_block`: product of the twisted-factor values
    times the quotient value;
  - GA3 `conditionalPairEpsilonValue_twistedFactor`: identifies the
    `(i, j)`-factor with the `(i+j, 0)`-factor;
  - GA2 `quotientValue_eq_monomial`: the quotient value is `c q^(-ds)`.

## Provenance

Henniart 2002 (`henniart-2002-characterization`), §2.4, enters only through the
published hypothesis `BlockPairGamma F`. The remaining steps are derived
comparisons and the identity theorem for rational functions on infinite sets.
