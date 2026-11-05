# Geometry of actual frame projective bundles

This internal derivation uses the existing actual `frameBundle`, its
Cartesian projective charts, and properness of the actual
`RelativeProjectiveSpace.toBase`. It introduces no literature assertion
or additional geometric existence premise.

`FrameBundle.toBase_property_iff` detects every morphism property local
at the target for the Zariski topology on the structure morphism of a
fixed finite-rank frame bundle. The local tests are the relative
projective-space projections over every frame-bearing base open.
The forward implication uses the existing Cartesian chart square.
The reverse implication uses the frame cover of the original base and
the square's canonical pullback isomorphism to identify each tested
base change with that projection.

`FrameBundle.isProper_toBase` applies this equivalence to properness.
Each projection is already proved proper, so the actual glued frame
projective bundle is proper over the base, for an arbitrary base scheme
and arbitrary projective dimension in the same universe.
`FrameBundle.properOver` bundles this actual scheme and its structure map
as an object of `Over S`, together with the proved properness of that map.
It uses the existing glued scheme, with no replacement or choice of a
different proper model.

`isProper_evaluationMap` assumes properness of the actual source
structure map and pointwise generation of every chosen local frame
evaluation. The existing global evaluation factors that structure map
through the frame bundle. Properness of the frame bundle implies its
separatedness over the base. Cancellation of the separated
postcomposition therefore proves properness of the actual evaluation
morphism.

This does not prove that evaluation is a closed immersion. Generation,
finite local rank and properness of the source remain explicit
hypotheses; the ordinary moduli theorem is not a conclusion.
