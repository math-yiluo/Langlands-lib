# Noetherian approximation for uniform exponents

This internal reduction restricts the uniform-exponent problem to affine
noetherian bases. The proposition `NoetherianAffineStatement` retains all
the original group hypotheses and asserts one positive exponent on all test
schemes. Its truth remains a hypothesis in this module.

For a finitely presented scheme model, local quasi-finiteness descends to a
finitely generated coefficient subalgebra. The implementation uses the
published descent of pure fibre dimension, with dimension zero, and the actual
cofiltered limit of the spectra of all finitely generated subalgebras. It
compares the relative base-change morphism used by that theorem with the
structural pullback morphism through pullback symmetry and an identity
pullback.

The main reduction first descends the underlying scheme to finite coefficients
over the prime subring of the original ring, then descends its full group law
using the published general group-scheme descent theorem. Commutativity is
retained. A further finite coefficient extension gives local quasi-finiteness.
All these coefficient rings are noetherian by the finite type theorem.
Finite presentation survives every scalar extension. An isomorphism identifies
the original group with the base change of the resulting noetherian model.
Any exponent on the model therefore kills every point of the original group.
Combining this argument with the finite affine-cover reduction gives the
unchanged quasi-compact-base target conditionally on the noetherian assertion.

This is an internal elaboration of the noetherian reduction in SGA 3, Exposé
IX, proof of Lemma 6.1 and footnote 40, printed p.53 (retained PDF p.23),
registered as `sga3-expose-ix-gille-polo-2009`, SHA256
`7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`.
The implementation reuses the published finite-presentation scheme and group
law descent theorems and pure-fibre-dimension descent. It imposes no flatness,
separatedness or affineness hypothesis on the group.
