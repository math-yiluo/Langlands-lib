# Actual reversed-dual Jacquet coefficient realization

This is internal derived content using the published actual reversed-dual
section transport `twoBlockDualSectionJacquet`, coefficient models, ordinary
Jacquet realization, and `unfoldedJacquetSeries_eq`. It adds no source
translation or analytic functional equation.

`transportedSecondDualFunctional` transports the Weyl-translated second dual
functional by the inverse of an actual representation equivalence. The
coefficient theorem uses the intertwining law to identify its coefficient at
`E v` with `secondDualFunction` of the original coefficient at `v`. The
nonvanishing theorem uses surjectivity of `E` and the published nonvanishing
of the Weyl-translated functional. The construction also permits zero original
functionals.

`reversedDualBlocks_whittakerType` preserves full Whittaker type for the
reversed inverse-transpose block family, with the negated additive character.
It uses the published inverse-transpose type theorem and the equality between
the standard character for `psi.scale (-1)` and the inverse character for
`psi`. Thus admissibility, finite generation and the full functional line are
retained; irreducibility is not assumed.

`exists_reversedDualJacquetRealization` applies the published section theorem
to the actual normalized lower induction. It assumes only smoothness of the
blocks for this carrier construction. The existential representation
equivalence precedes every additive character, block functional, additive
Haar measure and original induced functional. Both block sizes, their
dependent carriers and their representations are reversed. The new blocks
are the inverse-transpose pullbacks, and their inverse functionals are
`secondDualFunctional` of the corresponding original block functionals.

The original induced functional `J` must satisfy the explicitly stated
ordinary Jacquet coefficient identity for every actual section and group
element. This hypothesis is the identity supplied by the published ordinary
Jacquet existence theorem when its hypotheses hold. The new theorem is
conditional on this identity and does not independently construct an
ordinary functional at arbitrary parameters.

For this `J`, the theorem defines `JD` by transporting its second dual
functional through the actual section equivalence `E` and proves:

- Every coefficient at an arbitrary reversed-dual section `fD` is the actual
  `secondDualFunction` of the original coefficient at `E.symm fD`.
- `JD` realizes the ordinary reversed-dual Jacquet integral at every `fD`
  and every ambient group element.
- If `J` is nonzero, then `JD` is nonzero.
- Absolute integrability of the reversed-dual section is equivalent to
  absolute integrability of its actual inverse image under `E`.
- The actual unfolded series equals the equal-rank determinant-slice series
  of that dual coefficient, for every supplied Borel quotient measure,
  standard-character test function and Schwartz–Bruhat row test.

The rectangle measures come from the same arbitrary supplied additive Haar
measure: their dimensions are respectively `(m 0 + 1, m 1 + 1)` and
`(m 1 + 1, m 0 + 1)`. No measure is replaced by a proportional or newly chosen
one. The proof uses the published equality of Jacquet integrals and
absolute-integrability equivalence, evaluates the coefficient-transport
identity at each group element, and substitutes the resulting realization
into `unfoldedJacquetSeries_eq`. The section-series statement concerns total
restricted Bochner integrals and assumes no outer-slice convergence. Zero
original and block functionals are allowed; nonzero `J` is needed only for
the stated nonvanishing implication. Field and block-carrier universes are
independent.

No parameter continuation, Fourier coefficient identity, analytic block
functional equation, rational comparison or final dominant-rank gamma/L
proposition is asserted. No uniform support bound or convergence of the
outer series is asserted.

The canonical local instances have explicit `dualJacquet` names, so this module
can be imported together with the ordinary coefficient-model realization module
without a generated-declaration-name collision. Their values and the mathematical
declarations are unchanged.
