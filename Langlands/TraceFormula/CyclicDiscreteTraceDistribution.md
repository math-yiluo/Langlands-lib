# The discrete trace sum on the actual norm-one general linear group

Arthur and Clozel, *Simple Algebras, Base Change, and the Advanced Theory of
the Trace Formula* (1989), II §9, (9.2)–(9.3), printed p. 132, gives the
norm-one discrete distribution as a finite sum of operators and identifies
it with a locally finite character expansion. III (4.1)–(4.2), printed
pp. 203–204, specifies the operator order on the cyclic arithmetic component.

`discreteTraceOperator` composes actual operators on the supported Hilbert
slice in the order `M(s,0) T ρ(f)`. The integrated right action uses the
actual norm-one subgroup. `DiscreteTraceData` uses the full discrete
inducing space for each actual Levi. `IsSpectral` requires the genuine
compact picture, right translation, and global intertwining at zero.
`IsOrdinary` sets the twist equal to the identity. `IsArithmetic` uses
arithmetic pullback by the inverse field automorphism on sections.

`normOneTrace` sums these operator traces against the internal-to-ambient
Weyl order ratio and the reciprocal absolute determinant of the regular
Weyl element on the split component modulo the ambient centre. The same
sum applies over the base and upper fields. Its test space is the span of
restrictions of the usual compact smooth adelic tests that are finite
under left and right translation by the infinite compact.

`CyclicDiscreteTraceDataStatement` gives the existence interface for
spectral data in both specializations. `CyclicNormOneTraceClassStatement`
requires the actual summands to be trace class and the sum to give a
complex-linear functional on the norm-one test space. The interface
allows a supplied bounded twist since the trace-class argument applies
to the integrated action and trace class is an operator ideal.
