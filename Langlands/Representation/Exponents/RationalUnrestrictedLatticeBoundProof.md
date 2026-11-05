# Rational unrestricted lattice coefficient bound

`Langlands.Plancherel.rationalUnrestrictedLatticeBound.{u,uV,uI}` proves the
whole `RationalUnrestrictedLatticeBoundStatement`, retaining its simultaneous
standard-basis premise and independent field, carrier and coordinate universes.
This is an internal derivation.

The empty standard index needs no general standard-cocharacter-existence
assumption: `isStandardCocharacter_empty_self` supplies the given cocharacter
itself. The helper
`RationalCoefficientDecay.uniformizer_mem_chambers` then places every
nonnegative integral combination of the supplied weakly dominant cocharacters
in the actual split component's weak chamber. Only the non-strict clauses of
that helper are used. The argument uses no strict Jacquet exponent hypothesis.

For each smooth input pair, choose a common compact open fixing subgroup from
the supplied basis. The basis's empty-standard member gives opposite Iwahori
factorization, weak-chamber contraction in the upper and lower directions,
and invariance of the Levi intersection. These are exactly the explicit
hypotheses of `unrestrictedCompressedLatticeBound`. That theorem supplies a
product exponential estimate for the original coefficient.

Finally `compactTranslateLatticeBound` applies the finite-orbit argument to
both outer compact sets and the finite middle translate. Its coordinate
weights are zero, so its additional strict weighted inequalities are
identities independent of the radii. The final conclusion discards those
inequalities and retains positive radii and a positive coefficient constant.
This includes central directions and relative rank zero.

This proof establishes neither existence of the simultaneous standard basis
nor a Cartan cover or a comparison between coordinate growth and the actual
matrix norm. Those remain separate prerequisites for the full coefficientwise
moderate-growth target.
