# Maximal torus preimages in relative central quotients

Worker 226.

`Langlands.GroupScheme.RelativeCentralQuotientPreimageReductionStatement.{u}` is the named `Prop`-valued statement recording
the full reverse relative maximal-torus construction with the same explicit quotient-existence, reductivity and multiplicative-type-kernel hypotheses.
`Langlands.GroupScheme.relativeCentralQuotientPreimageReduction` proves this proposition by the existing helper theorem.
The helper signatures and all mathematical hypotheses are retained; the
other results below are proved companion helpers.

This internal assembly unit proves the reverse maximal-torus construction
for a supplied central quotient of reductive groups over any scheme,
assuming `RelativeCentralMultiplicativeTypeQuotientStatement` and a closed
central multiplicative-type kernel. Both ambient groups are assumed
reductive. The output is an actual closed relative torus, maximal on all
residue fibres, whose range is the full preimage of the given target
torus range.

First, `SubgroupPreimage.isRelativeTorus_of_maximalImage` shows that one
known relative-torus preimage of a maximal target torus suffices for all
maximal target tori. Published étale local conjugacy supplies target
conjugators. Each lifts along the fppf ambient homomorphism after another
fppf base change. Compatible inner automorphisms identify the actual
preimage with a conjugate of the known source torus, using
`RelativePreimageConjugacy`. Fppf descent recovers the relative-torus
property on the original base.

`SubgroupPreimage.isRelativeTorus_of_centralMultiplicativeTypeQuotients`
uses published étale local existence of source maximal tori. The forward
image construction provides one maximal image and its exact torus
preimage on each member of this cover. The preceding comparison and fppf
descent therefore apply to the actual preimage of the prescribed target
torus.

`SubgroupPreimage.isFibrewiseMaximalTorus_of_isRelativeTorus` handles
maximality once the actual preimage is known to be a relative torus.
Its projection to the prescribed target torus is flat and surjective.
Precomposition by this fpqc torus homomorphism does not change a torus
centralizer. Source centralizer points map into the target centralizer,
which is the target maximal torus itself. The exact preimage description
then shows that the source torus is self-centralizing. This equality
commutes with residue base change, where the published self-centralizing
criterion gives maximality.

The final existential theorem packages the actual preimage and these
properties. This unit is conditional on quotient existence, the
multiplicative-type kernel, and target reductivity; it does not discharge
those separate inputs or the full relative central quotient target.
