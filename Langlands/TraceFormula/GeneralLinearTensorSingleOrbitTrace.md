# The simple trace formula for one tensor test isolating one rational class

`generalLinearTensorSingleOrbitTrace` assumes that, for the given field and rank, the cuspidal
integrated actions of all tensor tests are Hilbert–Schmidt, as required by the tensor simple
trace formula. `generalLinearTensorCuspidalHilbertSchmidt_of_pos` proves this in positive rank.
Let `f = a ⊗ b` be the tensor of a smooth compactly supported archimedean kernel `a` and a
locally constant compactly supported finite test `b`, such that `b` integrates to zero along
all two-sided translates of all two-block unipotent radicals at a finite place `w`, and the
support of `f` is regular elliptic at a finite place `v`. Suppose every rational norm-one
element with a conjugate at which the positive average `f¹` of `f` does not vanish is
rationally conjugate to `r₀`. Then the operator `R(f)` on `L²` of the positive rational
quotient is trace class, the volume of the measures `d₀` at `r₀` is finite when the orbital
integral of `f¹` is nonzero, and `tr R(f)` equals the volume times the orbital integral of
`f¹` at `r₀`, for every choice `d₀` of compatible measures.

The proof applies the tensor simple trace formula, obtained from
`generalLinearTensorSimpleTraceFormula_of_simpleTraceFormula` with
`generalLinearSimpleTraceFormula` and `generalLinearRadicalIntegralVanishing`, to the
one-term family `f`. The geometric side is a sum over finitely many regular elliptic rational
classes, whose centralizers are commutative (`generalLinearRegularCentralizerCommutative`).
`singleOrbitGeometricTrace` reduces it to the single class of `r₀`.

The hypotheses on the cuspidal factor and regular elliptic support implement the ordinary
simple trace formula of Arthur–Clozel (1989), Chapter 1, Lemma 2.4, on the Library's positive
rational quotient. The one-orbit specialization is used in the proof of their Lemma 6.5.
