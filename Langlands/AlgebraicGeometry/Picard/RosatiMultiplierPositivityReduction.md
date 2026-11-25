# From actual Rosati positivity to positive self-isogeny multipliers

This internal reduction uses the existing actual rational Hom category,
constructed dual, geometric polarization, Rosati conjugation and fixed geometric
trace. It preserves the single arbitrary universe parameter `u`.

`MultiplierPositivityReductionStatement` is the Prop-valued definition
`PositivityStatement.{u} → MultiplierPositivityStatement.{u}`. It records the
conditional reduction with both existing statements unchanged. The theorem
`multiplierPositivity_of_positivity` in this module implements that implication.
This module states this internal reduction and supplies its helper lemmas;
it is not a proof of the unconditional multiplier statement, which
`multiplierPositivity` in `RosatiMultiplierPositivityProof` derives from this
reduction.

`involution_mul_self_of_pullback` takes exactly the existing
`IsRationalDualPullbackMultiple` equation for an actual rational endomorphism
`f`, the same integral polarization on both sides, and a rational scalar `q`.
It requires the existing `HasRationalInverse` construction instance. Composing
the equation with `polarizationInverse` and using associativity gives
`involution f * f = q • id0 A`. The order agrees with the existing endomorphism
algebra: multiplication applies the right factor first. No pairing equation
replaces the actual dual-pullback equation.

`multiplierPositivity_of_positivity` proves the implication from the full
existing `Rosati.PositivityStatement` to the full existing
`Rosati.MultiplierPositivityStatement`. This is a conditional reduction; it
does not prove the unconditional multiplier target. The unchanged positivity
statement is proved separately, by `positivity` in `RosatiPositivityProof`.

The proof derives the rational-inverse instance from the published
`Rosati.rationalInverse` theorem applied to the actual geometric polarization.
The rational self-isomorphism has nonzero forward map, since composing a zero
forward map with its inverse would contradict `id0 A ≠ 0`.
Actual rational dualization preserves identity by `dualHom0_id`, so Rosati
conjugation fixes `id0 A`. The strict positivity clause at the identity
therefore gives positive geometric trace of the identity. The same clause at
the forward map gives positive trace of `f * involution f`. The published
`geometricEndomorphismTrace_mul_comm` and the norm equation identify this trace
with `q * geometricEndomorphismTrace A (id0 A)`. Rational linearity of the fixed
trace and elementary ordered-field arithmetic yield `0 < q`.

This argument needs no full algebra anti-involution theorem and no full
geometric trace-comparison theorem as additional premises. The imported trace
cyclicity theorem handles both branches of the fixed trace construction,
including its zero fallback; strict positivity is the explicit premise that
drives this reduction. All construction prerequisites and hypotheses of the
original multiplier target remain inside its conclusion without alteration.

The provenance is an internal consequence of the imported constructions and
published helper theorems. Its mathematical motivation is the derivation in
the paired multiplier statement from Milne, *Abelian Varieties*, January 2,
2022 author revision, section 17 and Theorem 17.3, printed/PDF pages 35–36.
The original pages, the trace comparison discussion on pages 23–24 and the
complete registered errata snapshot were read. The reduction claims no new
independent theorem from that source.
