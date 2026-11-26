# Conjugate self-duality of a weak induction, totally complex rigidity premise

Module `Langlands.Global.Arithmetic.HarrisWeakInductionConjugateSelfDualTCProof`.

`Langlands.Global.Harris.weakInductionConjugateInverseSelfDualTC` proves exactly
`Langlands.Global.Harris.WeakInductionConjugateInverseSelfDualTCStatement.{uV, uE, uE'}`,
with independent universes `uE` and `uE'` for the CM fields `E` and `E'` and `uV` for the
carrier of spectral presentations, and no hypothesis beyond those of the statement. The
premise is the totally complex rigidity statement `CuspidalSpectralRigidityTCStatement.{uE, uV}`;
no unrestricted rigidity statement is assumed.

## Source

Harris (1998), *The local Langlands conjecture for GL(n) over a p-adic field, n < p*,
Invent. Math. 134, 177–210 (registered source `harris-1998-local-langlands`),
Proposition 4.8, stated on printed p. 201 (`math_9611226v1.tex` lines 1554–1563, hypothesis
`ξ = ξ⁻¹ ∘ c` at lines 1558–1559). See `HarrisWeakInductionConjugateSelfDualProof.md` for the
source of the conjugate self-duality argument (proof of Lemma 1.6, printed p. 188, lines
741–746).

## Implemented proof

The core result
`Langlands.Global.Harris.isConjugateSelfDual_of_isWeakAutomorphicInductionOf_of_isConjugateInverse`
(module `Langlands.Global.Arithmetic.HarrisWeakInductionConjugateSelfDualProof`) needs
only Euler constituent recovery at the base field `E`. The premise supplies it as its third
component, `CuspidalEulerConstituentRecoveryTCStatement.{uE, uV}`, applied at `E`. Its
instance argument `[NumberField.IsTotallyComplex E]` is found from `[IsCMField E]`, because
a CM field is totally complex (Mathlib's instance `IsCMField.isTotallyComplex`). The
core result then gives `c.IsConjugateSelfDual`, with the full conjugate-contragredient
pairing.
