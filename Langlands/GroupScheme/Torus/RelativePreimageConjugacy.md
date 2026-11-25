# Torus preimages, conjugacy, and fppf locality

`Langlands.GroupScheme.SubgroupPreimage.RelativeTorusPreimageConjugacyStatement.{u}` is the named `Prop`-valued statement recording
relative-torus preimage transport through compatible ambient isomorphisms.
`Langlands.GroupScheme.SubgroupPreimage.relativeTorusPreimageConjugacy` proves this proposition by the existing helper theorem.
The helper signatures and all mathematical hypotheses are retained; the
other results below are proved companion helpers.

This internal module supplies actual-scheme tools for the reverse torus
construction in `RelativeCentralQuotientStatement`.

The module imports the published `baseChange_innerIso_hom` comparison for
inner automorphisms.

`exists_fppf_baseChange_section_lift` lifts any base section of the target
of an fppf group homomorphism after one fppf base change. The base change
is the actual scheme pullback along that section. The lift uses the
base-point adjunction, and the pullback equation verifies its image.

`SubgroupPreimage.isRelativeTorus_of_fppfCover` descends the relative-torus
property for actual subgroup preimages. Actual group pullbacks commute
with base change, so the published fppf relative-torus descent theorem
applies to their canonical comparison isomorphisms.

`SubgroupPreimage.isRelativeTorus_of_conjugate_image` assumes a closed
relative torus is the full preimage of a supplied closed subgroup. If a
pair of ambient isomorphisms commutes with the quotient homomorphism and
the target isomorphism carries that subgroup range to a second closed
subgroup range, its preimage is a relative torus as well. The proof
transports the full preimage equality through inverse isomorphisms and
uses the uniqueness isomorphism between subgroup representatives.
No central-kernel, smoothness, reductivity, or maximality assumption is
needed for this transport step.

These are derived tools, not a proof of the full central quotient target.
