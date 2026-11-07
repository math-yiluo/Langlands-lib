# Translation of actual unramified rational scalars

This derived construction extends the existing regular parameter translation to
scalar presentations and to the existing actual unramified function field. It
also identifies coefficient extraction from a translated rational operator with
translation of its extracted fraction. It contributes the scalar part of the
parameter comparison needed when changing the base representation of an
unramified twist orbit.

## Source and provenance

The motivating source is J.-L. Waldspurger, *La formule de Plancherel pour les
groupes p-adiques (d'après Harish-Chandra)*, IV.1, printed pp.276–277 / PDF
pp.42–43, registered as `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
There the orbit is parameterized by twists of a fixed representation, a rational
scalar is specified by a regular numerator and a denominator nonvanishing on its
region, and rational operator families use one denominator for all input
vectors. The evaluations `b_m(χ) = χ(m)` generate the regular functions used in
the family construction.

The present translation and fraction-field compatibility are derived algebraic
constructions, rather than a transcription of a separately numbered source
assertion. Their proof uses the existing evaluation-generated algebra,
`UnramifiedOperatorTranslation`, `RationalUnramifiedScalarField`, and Mathlib's
`IsFractionRing.ringEquivOfRingEquiv`. The original source works on an orbit of
isomorphism classes; this module works on its actual character parameter space.
The representation comparison and stabilizer invariance needed to descend to
that orbit remain separate obligations.

## Generic regular functions and scalar presentations

Let `L` be an arbitrary topological group and `ν` an arbitrary indexed family of
positive real unit-valued characters. Write `X = unramifiedCharacters ν` and
`B = unramifiedRegularFunctions ν`. For `τ ∈ X`, the imported
`unramifiedRegularTranslation ν τ` is the complex algebra automorphism

`T_τ(b)(χ) = b(τ * χ)`.

`unramifiedRegularTranslation_one` and
`unramifiedRegularTranslation_mul` prove its identity and composition laws. In
Lean the latter says `T_(τ*σ) = T_τ.trans T_σ`: applying the left side to `b` and
then evaluating at `χ` gives `b((τ*σ)*χ)`, while the right side gives
`b(τ*(σ*χ))`. Both proofs use extensionality and the corresponding group law.

A `UnramifiedOperatorFamily.ScalarPresentation Ω f` consists of `a,b ∈ B`,
nonvanishing of `b` on `Ω`, and `b(χ) * f(χ) = a(χ)` there. Its new
`ScalarPresentation.translation p τ` has numerator `T_τ(a)`, denominator
`T_τ(b)`, and region

`Ω_τ = (unramifiedParameterTranslation ν τ) ⁻¹' Ω`.

The represented value at `χ ∈ Ω_τ` is `f(τ*χ)`, with membership carried by
`unramifiedTranslationPreimageEquiv`. Nonvanishing and the clearing identity
follow by evaluating the original presentation at exactly that parameter. The
numerator and denominator projection identities are definitional. No
nonemptiness or openness assumption is needed for this generic construction.

## The existing actual function field

For the remaining declarations, `F` is an arbitrary nonarchimedean local field,
`G` is a group scheme over `F`, and its rational points have the given topology.
The explicit premises are continuity `hp` of the rational valuation-image
projection and connected reductivity `hG`. They are precisely the inputs of the
existing `rationalUnramifiedFunctionField G hp hG`; the field characteristic is
unrestricted. Here `ν(ψ) = (rationalNormCharacters G ψ).toMul`.

`rationalUnramifiedFunctionFieldTranslation G hp hG τ` extends `T_τ` to a ring
automorphism of that existing field, using Mathlib's fraction-ring extension of
a ring equivalence. The `_algebraMap` theorem gives the exact regular-function
compatibility. Consequently the extension sends the embedded fraction `a/b` to
the embedded fraction `T_τ(a)/T_τ(b)`. The `_constant` theorem proves that it fixes
complex constants embedded first in the regular algebra and then in the field.
This statement uses those existing embeddings and does not introduce another
complex scalar structure on the fraction field.

The `_one` and `_mul` theorems prove the identity and composition laws by lifting
the corresponding regular algebra laws with Mathlib's fraction-ring identity
and composition theorems. The fraction field has its previously established
faithful regular-function embedding and domain-based field structure; no
evaluation of an arbitrary fraction at a pole is defined here.

`ScalarPresentation.translation_toFunctionField` identifies the fraction
represented by the translated presentation with translation of the original
fraction. Its two nonemptiness arguments may be chosen independently. The
proof rewrites both presentations as their embedded numerator divided by their
embedded denominator, uses preservation of division, and applies regular-map
compatibility. Nonempty regions ensure that both presentation denominators are
nonzero as regular functions through the imported presentation API.

## Rational operator coefficients

`rationalUnramifiedOperatorScalar_translation` considers an arbitrary complex
module `V`, an operator family `A : Ω → Module.End ℂ V`, a whole-operator
rationality proof `hA`, and an independently supplied rationality proof `hAτ` for
the family `χ ↦ A(τ*χ)` on `Ω_τ`. The translated rationality follows from the
imported `isRationalOperatorOn_translation_iff`; allowing an independent witness
makes the conclusion independent of that construction's choices.

For any `v ∈ V` and complex linear functional `ℓ`, the theorem states that the
fraction extracted from `χ ↦ ℓ(A(τ*χ) v)` equals the function-field translation
of the fraction extracted from `χ ↦ ℓ(A(χ) v)`. Both extraction regions are
supplied as nonempty. There is also a nonempty ambient open set `D ⊆ Ω`, which
is the hypothesis required by the existing uniqueness theorem for extraction
from arbitrary presentations.

The proof translates `scalarCoefficientPresentation A hA v ℓ`. The preimage of
`D` is open under the parameter homeomorphism and nonempty by its inverse.
`rationalUnramifiedOperatorScalar_eq_presentation` therefore identifies the
independently extracted translated coefficient with this translated
presentation. `translation_toFunctionField` proves the claimed fraction
identity. Scalarity of `A` and normalization `ℓ(v)=1` are not premises; the
result compares ordinary extracted coefficients even when `A` is not scalar.
The group, character-index, field and module universes are independent wherever
their underlying interfaces permit.

## Retained obligations

This module does not construct the original standard intertwining integrals or
prove their convergence, rationality, or naturality. It does not prove generic
induced irreducibility, identify the actual twist-induction comparison for a
changed orbit base representation, establish stabilizer invariance or orbit
descent, or prove parabolic independence, nonvanishing, positivity, the globally
normalized `j` or `mu`, or a Plancherel conclusion. It supplies the scalar
parameter-translation identity to be combined with those representation and
analysis results.
