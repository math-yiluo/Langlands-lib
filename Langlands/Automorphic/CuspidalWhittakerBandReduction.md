# Actual multiplicity one from band estimates and analytic comparison

`CuspidalWhittakerBandReductionStatement.{u}` has the exact existing
`CuspidalOperatorMultiplicityOneStatement.{u}` as consequent and retains
two named premises: `CuspidalWhittakerBandBoundStatement.{u}` and
`CuspidalWhittakerBandSobolevComparisonStatement.{u}`. The number field
universe remains arbitrary and free; every natural rank parameter,
including r = 0, is included. The unconditional target is proved as
`cuspidalOperatorMultiplicityOne` (module
`Langlands.Automorphic.CuspidalOperatorMultiplicityOneProof`) through this
reduction: `cuspidalOperatorMultiplicityOne_of_bandMixed` applies it by way of
`cuspidalWhittakerBandSobolevReduction`, with the two premises supplied as
described below.

The first premise asserts the actual fixed-finite-level band derivative
bound for every unitary-center cuspidal realization and standard additive
character, at any supplied actual band-integrability witness. For each
compact open finite subgroup J and compact adelic set Q, it supplies
finitely many genuine enveloping derivatives and a nonnegative constant,
uniform over the J-fixed original vector and point of Q. The norm is
exactly the determinant-band rational-quotient Haar L² norm. This premise
is not proved here; the module `CuspidalWhittakerBandSobolevReduction`
supplies it from the compact Sobolev estimate.

The second premise takes two such actual unitary-center realizations, a
full finite/compact/differential operator equivalence, a standard additive
character, actual band-integrability witnesses and the two band bounds.
It concludes one complex scalar comparing the actual Whittaker
coefficients along the supplied equivalence, uniformly over every
original vector and adelic group point. No theorem of the Library has this
analytic comparison as its type; `cuspidalBandComparison_of_mixedUniqueness`
(module `Langlands.Automorphic.CuspidalBandMixedMultiplicityOneReduction`)
derives it from mixed Whittaker uniqueness, which the Library obtains as
`cuspidalBandMixedWhittakerUniquenessFromLocal` applied to
`Archimedean.unitaryWhittakerMultiplicityOne`.

The implemented reduction invokes the published unitary-center
normalization, chooses the published standard global additive character,
and constructs actual band-integrability witnesses from cuspidality and
the published band cover. It applies the first premise on both sides,
then the second premise. Published actual Whittaker reconstruction gives
equality of the original realizations. There is no extra hypothesis in
the exact consequent.

The supporting modules prove compact domination of actual Whittaker
coefficients and a conditional comparison with supplied orbit-derivative
seminorms. The latter first expands actual enveloping operators as finite
linear combinations of real Lie words. A supplied generator-compatibility
identity identifies these words with iterated orbit derivatives, and a
supplied norm identity identifies the actual band norms with the image
norms. These hypotheses are explicit: the estimate applies to the image
of original J-fixed vectors and constructs no Hilbert globalization.

This is an internal derived reduction and its supporting estimates. Shalika, *The multiplicity one theorem for GL_n*
(1974), Theorem 5.5 and Lemmas 5.6–5.9, printed pp.187–189, motivate the
unitary-center normalization, compact estimates and coefficient comparison.
The formal proof reuses published Library constructions rather than
asserting that Shalika's group representations and center-quotient norm
are already identified with the operator realization and band norm.

Compatible full-group Hilbert globalizations, smoothness and density in
the required derivative topology, extension and equivariance of the
actual coefficient functionals, and continuous local and all-place
uniqueness are substantive parts of the second premise.
An invariant positive form and the proved finite seminorm bound do not
alone establish these results. The compact Sobolev statement
`OperatorCompactSobolevStatement` and its proof `operatorCompactSobolev` are in
separate modules.
