# Unitary extension of an arbitrary finite local character

Author: Worker 5167.

`Langlands.Global.unitaryLocalCharacterExtension.{u}` proves the unchanged
published proposition
`Langlands.Global.UnitaryLocalCharacterExtensionStatement.{u}`.
For every number field `F : Type u`, finite place `v`, and continuous
character `χ : (FiniteCompletion F v)ˣ →ₜ* ℂˣ` with all complex values
of norm one, it constructs a unitary `HeckeCharacter F` whose full
`finiteComponent v` equals `χ`. The field universe remains arbitrary.

The proof composes three published arithmetic constructions. All characters
use the actual adic completions and their unit-group topologies, and the
global characters are continuous characters of the actual idele-class
quotient. No new arithmetic or topological premise is introduced.

## Match the integral units

Let `O = v.adicCompletionIntegers F`. The continuous homomorphism `i` in
the proof is exactly `Units.map O.subtype.toMonoidHom`, equipped with
continuity of the subring inclusion on units. Restrict `χ` along `i`.
The theorem `Langlands.Global.integralUnitCharacterExtension` from
`Langlands.Global.Arithmetic.IntegralUnitCharacterExtensionProof` supplies
a continuous local character `η`, an exponent `n > 0` with `η ^ n = 1`,
and agreement `η (i b) = χ (i b)` for every `b : Oˣ`.
Only this matching character is required to have finite order.

Apply `Langlands.Global.finiteOrderCharacterPrescription_proof` from
`Langlands.Global.Arithmetic.CharacterPrescriptionProof` to the singleton
finite set `{v}`, with local character `η` and trivial character of the
whole infinite idele factor. It gives an actual Hecke character `ψ` with
`ψ ^ (2 * n) = 1` and `ψ.finiteComponent v = η`. Evaluation of the power
identity followed by `Complex.norm_eq_one_of_pow_eq_one` proves
`ψ.IsUnitary`, since `2 * n > 0`.

## Correct the unramified quotient

Put `δ = χ / ψ.finiteComponent v`. The norm of every value of `δ` is
one, by division of the two norm-one values. To verify triviality on
integral units in the exact subgroup convention used by the norm-power
construction, take a field unit `a` such that both `a` and its inverse
belong to `O`. These two membership proofs define a unit `b : Oˣ` whose
image under `i` is exactly `a`. The restriction identity and the equality
of the prescribed component therefore give `δ a = 1`.

The theorem
`Langlands.Global.HeckeCharacter.exists_unitaryNormPower_finiteComponent`
from `Langlands.Global.HeckeNormTwist` supplies `t : ℝ` with
`(HeckeCharacter.unitaryNormPower F t).finiteComponent v = δ`.
This construction uses the imaginary power `exp(i t log |x|)` of the
actual idelic norm, which is globally unitary. Its local comparison
identifies the whole unramified character, including its value on a
valuation generator.

The required character is
`ψ * HeckeCharacter.unitaryNormPower F t`. Multiplication of norm-one
values proves global unitarity. The theorem
`HeckeCharacter.finiteComponent_mul` and cancellation yield the exact
identity of continuous homomorphisms
`ψ.finiteComponent v * (χ / ψ.finiteComponent v) = χ`.
The input `χ` may have infinite order; the norm-power correction retains
its arbitrary unramified unitary part.

## Provenance

The extension assertion appears at the end of Section 2.8 of Guy Henniart,
*Une preuve simple des conjectures de Langlands pour GL(n) sur un corps
p-adique*, Inventiones Mathematicae 139 (2000), printed p.448 (retained
PDF p.10); the unitary-character convention is in footnote 1 on printed
p.439. Registered source: `henniart-2000-simple-proof`, SHA256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.

The implemented proof is a derived composition of the three Library
theorems named above. Their paired Markdown documents the local compact
unit and valuation-splitting argument, the doubled-exponent finite-order
prescription theorem, and the idelic norm construction. This proof uses
their proved conclusions directly. It does not follow the general
closed-subgroup character-extension route suggested by the target's
Markdown and uses no downstream relative isometry, local Langlands
correspondence, or Henniart globalization theorem.
