# A common scalar norm parameter for integral segment heads

Authors: Worker 320 (complete Lean draft and initial explanation) and
Worker 438 (dependency audit, expanded explanation and submission).

`Langlands.Classification.integralSegmentHeadScalarNorm` proves exactly
`Langlands.Classification.IntegralSegmentHeadScalarNorm.{uF,uV} F T` from
[IntegralSegmentHeadScalarNormStatement](IntegralSegmentHeadScalarNormStatement.md).
Its outer parameters are `{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)`
and `(T : F.TopologicalData)`. The field and representation universes remain
independent; cuspidal representatives and head carriers have the statement's
saturated universe `max uF uV`. All topology and absolute-value data come
from the supplied `T`.

Fix a cuspidal datum `ρ` of rank `r > 0`. The proof chooses one `t : ℝ`
such that, for every actual segment `Δ` with inclusive integral coordinates
`[b,a]` on the line through `ρ`, and every supplied strong head `π` of `Δ`,
there is a monoid homomorphism `c : F.Carrierˣ →* ℂˣ` acting by scalars on
every vector of `π` and satisfying

\[
 \|c(z)\|=|z|^{\deg(\Delta)(t+(a+b)/2)} .
\]

Here `|z| = T.normalizedAbs z`. The choice of `t` precedes the segment,
both endpoints and the head. The proof constructs neither a head nor an
interval; it applies to the actual data quantified in the statement.

## The common parameter

`Quotient.exists_rep ρ.cls` supplies an actual supercuspidal representative
`A` of the given isomorphism class. The representative's defining properties
include irreducibility and admissibility. The published
`admissibleSchur_centralCharacter` gives a character of the full center
acting by scalars. Composing it with `GeneralLinear.scalarToCenter` gives
`ω : F.Carrierˣ →* ℂˣ` and its exact scalar action on `A`.

Irreducibility makes the associated group-algebra module simple, hence
nonzero. The published `HasScalarCharacter.isOpen_ker` applies to the
smooth representation `A.obj`, this scalar action and the continuous map
`GeneralLinear.scalarContinuous`. It proves that `ω.ker` is open using the
stabilizer of a nonzero vector. The proof then sets

\[
 s=-\log_q\|\omega(\varpi)\|,\qquad t=s/r,
\]

where `q = T.residueCardinality` and `ϖ = T.uniformizerUnit`. The published
`T.norm_eq_normalizedAbs_rpow_of_isOpen_ker` proves
`‖ω(z)‖ = |z|^s` for every unit `z`. Only after defining this `t` does the
proof introduce `Δ`, `b`, `a` and `π`.

## The actual quotient character

Write `m = Δ.length`. The coordinate hypothesis supplies
`Δ.base = ρ.twist b` and `a = b + m - 1`; the proof substitutes the first
equality. It twists the same actual representative `A` by
`T.determinantPowerCharacter r b`, obtaining `Ab`. The supplied open-kernel
and determinant-kernel lemmas make this an actual supercuspidal
representative, and the original representative equality proves that `Ab`
represents `ρ.twist b`.

`T.hasScalarCharacter_segmentFactor` gives its scalar character

\[
 \omega_b=\omega\cdot(\nu_r^b\circ\mathrm{scalar}),
 \qquad \nu_k^x=T.\mathrm{determinantPowerCharacter}\ k\ x.
\]

Apply the published `segmentConstituentCentralCharacter` to the segment
with base `ρ.twist b`, length `m` and representative `Ab`. The given strong
head implies the actual quotient relation via
`IsSegmentHead.isSegmentQuotient`. The constituent theorem therefore gives
the exact scalar action on `π` of

\[
 c=\omega_b^m\cdot
       (\nu_{mr}^{(m-1)/2}\circ\mathrm{scalar}).
\]

In that theorem, scalar action passes through an actual surjective
intertwiner. Changing the representative of the base uses the published
isomorphism of the actual segment inductions. Thus this step retains the
genuine quotient relation.

## Norm computation and provenance

The published `T.norm_determinantPowerCharacter_scalar` gives
`‖ν_k^x(z I_k)‖ = |z|^(k x)`. Since `z` is a unit, `|z| > 0`.
The norm of a product, the norm of a natural power and the real-power
addition/multiplication identities give

\[
 \|c(z)\|
 =|z|^{\,m(s+rb)+mr(m-1)/2}.
\]

After casting `a = b + m - 1` to the reals, positivity of `r` allows
division by `r`. The final `field_simp` and `ring` steps verify

\[
 m(s+rb)+mr(m-1)/2
   =mr\bigl(s/r+(a+b)/2\bigr)
   =\deg(\Delta)\bigl(t+(a+b)/2\bigr).
\]

This is the internal derivation proposed in the published target Markdown.
It combines published scalar-action and character-norm results with
arithmetic, and introduces no additional literature assertion. In particular,
the open-kernel helper imported from
[ProductLeviCentralCharacter](ProductLeviCentralCharacter.md) is the
stabilizer argument above; no analytic temperedness conclusion is used.
The conditional twist-freeness lemmas imported with integral coordinates
are unused. No unitarization, commutation, analytic integrability,
exhaustion or classification theorem enters the proof.
