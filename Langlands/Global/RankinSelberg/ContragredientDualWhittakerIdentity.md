# The Whittaker function of the dual cusp form

Module `Langlands.Global.RankinSelberg.ContragredientDualWhittakerIdentity`. Author:
Worker 381.

## Content

The module proves one theorem, in the namespace `Langlands.Global.RankinSelbergGlobal`:

```lean
theorem cuspWhittaker_inv_eq_dualFunction {r : ℕ}
    (T Td : Automorphic.CuspidalOperatorRealization F r) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (x : T.Space) (xd : Td.Space)
    (hxd : cuspFunction F Td xd = dualFunction F (r + 1) (cuspFunction F T x)) :
    cuspWhittaker F Td ψ⁻¹ xd = dualFunction F (r + 1) (cuspWhittaker F T ψ x)
```

for a number field `F : Type u` with `CompactSpace (AdeleQuotient F)`. Here `T` and `Td` are
any two actual cuspidal operator realizations of `GL_(r+1)`, `ψ` is a standard additive
character of `𝔸_F` (continuous, nontrivial, trivial on `F` and of absolute value one),
`cuspFunction F T x` is the cusp form `φ_x` on `GL_(r+1)(𝔸)` of the vector `x`,
`cuspWhittaker F T ψ x` is its `ψ`-Whittaker function `W_x` (all simple-root coefficients
one), and `dualFunction F n φ (g) = φ(w_n ᵗg⁻¹)`.

In words: **if the cusp form of `xd` is the dual cusp form `φ̃_x(g) = φ_x(w_n ᵗg⁻¹)`, then
the `ψ⁻¹`-Whittaker function of `xd` is the dual `W̃_x(g) = W_x(w_n ᵗg⁻¹)` of the
`ψ`-Whittaker function of `x`.** No relation between `T` and `Td` other than `hxd` is used.

## Source

J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004), registered as
`cogdell-2004-analytic-theory-gln` (PDF page = printed page + 3). On p.201 the Whittaker
model of the contragredient is `{W̃(g) = W(w_n ᵗg⁻¹)}` for the character `ψ⁻¹`; on p.207
"for `W ∈ W(π, ψ)`, we set `W̃(g) = W(w_n g^ι) ∈ W(π̃, ψ⁻¹)`", which for cusp forms is the
identity `W_(φ̃) = W̃_φ` proved here. Cogdell does not write out its proof; the proof below
is the change of variables `n ↦ w_n ᵗn⁻¹ w_n⁻¹` in the Whittaker integral, which the Library
has already carried out.

## Proof

Fix `y`. The published `Unfolding.dualCuspWhittaker_eq_setIntegral` for `T` and the standard
character `ψ⁻¹` (`isStandardAdditiveCharacter_inv`), after `inv_inv`, writes
`W̃_x(y) = dualFunction (cuspWhittaker F T ψ x) y` as the mass normalizer of `N(F)\N(𝔸)`
times the integral over the chosen fundamental domain of `N(F)` in `N(𝔸)` of
`φ̃_x(m y) · (ψ⁻¹_N(m))⁻¹`, where `ψ⁻¹_N = genericCharacter F r ψ⁻¹ (fun _ => 1)`.

On the other side, `cuspWhittaker F Td ψ⁻¹ xd y` is by definition the character
coefficient of `φ_(xd)` for `ψ⁻¹_N`, and the published
`subgroupCharacterCoefficient_eq_setIntegral` writes it as the same mass normalizer times
the integral over the same fundamental domain of `φ_(xd)(m y) · conj(ψ⁻¹_N(m))`. Its
hypotheses are the continuity of the generic character, its invariance under `N(F)`
(`genericCharacter_rational_mul`) and the left `GL_(r+1)(F)`-invariance of `φ_(xd)`
(`cuspFunction_rational_mul`).

Since `ψ` is unitary, `conj(ψ⁻¹_N(m)) = (ψ⁻¹_N(m))⁻¹` (`genericCharacter_inv` twice and
`genericCharacter_inv_eq_inv`). After this rewriting and `hxd : φ_(xd) = φ̃_x`, the two
expressions coincide.
