# The conductor of a trace character

`IsDifferentExponent.mem_additiveLattice_iff` identifies the trace
codifferent with the additive lattice at index `d`. The Lean proof
uses the Library's valuation of a uniformizing element, `exp(-1)`, to
rewrite the codifferent's defining integer-ring condition. Cancelling
`exp(-d)` gives the lattice condition. The codifferent convention is
that of Serre, *Local Fields* (1979), Chapter III, §3, printed p. 50,
literature ID `serre-1979-local-fields`.

For characters related by the field trace, take the annihilator of the
extension integer ring under multiplication and the extension character.
For any extension integer `y`, the annihilator condition also applies
to `a*y` for all base integers `a`, since the field map is continuous
and preserves integer membership. Trace linearity gives triviality of
the base character on every `a * Tr(x*y)`. The published integer-ring
annihilator theorem and base conductor zero then give integrality of
`Tr(x*y)`. Conversely, if all such traces are integral, the pullback
character is trivial on all products with `x`.

Thus the annihilator is exactly the codifferent. The published
annihilator theorem over the extension identifies it with the lattice
at the extension character's conductor. Surjectivity of the discrete
valuation identifies the two lattice indices, proving
`IsDifferentExponent.additiveConductor_of_trace`.
