# Ordinary simple trace formula on an isolated rational orbit

`GeneralLinearSingleOrbitTraceStatement` assumes the Library's
`GeneralLinearSimpleTraceFormulaStatement`. It takes the same
convolution, Hilbert–Schmidt, parabolic vanishing and support
hypotheses, for the same norm-one group and central split torus.
The specified representative comes with compatible orbital and
rational-centralizer measures. Every rational orbit on which the
positive-torus average has a nonzero value is assumed conjugate to
that representative.

The resulting trace on the actual adelic quotient equals the
rational centralizer covolume times the orbital integral at the
specified representative. The specified covolume is finite when
that orbital integral is nonzero. Integrability of the convolution
and trace class of its operator are inherited from the simple
trace formula.

The proof uses commutativity of the regular centralizers to supply
compatible measures for every representative in the simple trace
formula. It instantiates the two quotient measures with their
canonical Borel structures and applies the one-orbit reduction of
the resulting finite geometric expansion.

This internal reduction uses the Library's form of Getz–Hahn 2024,
Corollary 18.4.1, in the isolation step of Arthur–Clozel, Chapter 1,
Theorem 4.5.
