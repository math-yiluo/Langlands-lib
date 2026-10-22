# Conditional unequal-rank integral transport

This is internal derived content built on `UnequalRankCharacterTransport`,
the existing quotient measure-law predicate and Mathlib's measurable-equivalence,
product-measure and Bochner-integral APIs.

The rectangular row scaling S multiplies row i by a^(-(i+1)).
The expected pushforward multiplier is the positive real number

    c_rect = |a|^((n+1) * sum_{i=0}^{j-1}(i+1)).

`HasCharacterChangeRectangularMeasureLaw` explicitly assumes that the pushforward
of the specified rectangular measure is c_rect times that measure. This unit
defines the proposed multiplier and proves it is nonzero; it does not prove
that any chosen Haar measure has this law. The quotient measure law remains
the separate published predicate, with multiplier c_quot.

The product change is the actual measurable equivalence (q,x) ↦ (T_a q,Sx).
For S-finite measures, Mathlib's product pushforward theorem and the two
assumed measure laws give multiplier c_quot c_rect. Its nonzero finite value
and the measurable-equivalence integrability theorem give equivalence of
product integrability.

For the actual iterated unequal-rank integral, with rectangular integration
first, the proved formula is

    |det d_a|^(s - (j+k+1)/2) I_new(s) =
      c_quot c_rect I_old(s).

The proof moves the fixed complex multiplier through both total Bochner
integrals, substitutes the pointwise integrand identity, and applies the
rectangular and quotient change-of-variables formulas in that order.
This formula does not require S-finiteness or an integrability hypothesis.
The convergence equivalence uses the separate product-integrability argument
and therefore explicitly requires both measures to be S-finite.

Both statements use the actual corrected Whittaker coefficient transport
and the unchanged integration order. Zero measures are allowed.
No rational continuation or existence of a normalized local factor is asserted.
