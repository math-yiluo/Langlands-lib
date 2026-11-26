# Spanning the twisted irreducible spectrum

`TwistedPseudoCoefficientSpanningStatement` gives the spanning part of
the pseudo-coefficient splitting for \(GL_n(E)\) with `n > 0`. The
field `E` is a cyclic extension of a characteristic-zero nonarchimedean
local field `F` and uses its supplied `F`-module topology. For any Haar
measure and any representation `τ` used to define the unramified orbit,
the irreducible twisted distributions belong to the sum of the orbit
span, the other essentially tempered span and the proper-induction span.
The field and carrier universes are independent.

The stable standard traces span all irreducible twisted distributions.
When the standard shape has several blocks the trace belongs to the
proper-induction span by `temperedStandardTrace_mem_sigmaProperInducedSpan`.
A one-block standard trace is an irreducible essentially tempered trace,
which belongs to the orbit span or the other essentially tempered span
according to its underlying representation. The proof transports actual
twisting operators along equivalences of carriers when applying the
classification in its required universe and returning to the prescribed
span. The extension field uses its original module topology.

This is the spanning assertion used in Henniart–Lemaire (2011), II.5.10–II.5.13.
