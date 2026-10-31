# coarse-central evaluation for normalized refined induction

This internal construction specializes elementary function evaluation to
`T.normalizedRefinedInduced B S sigma`. It uses the public actual refinement
functors, flattened scalar identity and refined half-modulus calculation in
`Classification.MaximalConeLifting`. Field and carrier universes are independent.

`repeatCoarseScalars` sends a tuple `a` of outer block scalars to
`a` composed with `B.flattenOuter S`. `coarseScalarRefinedLevi` maps
this repeated tuple through the flattened block-scalar homomorphism and the
actual flattened-to-refined Levi equivalence. Its value in the ambient product
Levi is precisely `B.blockScalarLevi a`, by the public flattened scalar identity.
The auxiliary coordinate ring has its own universe.

`refinedCoarseCentralEvaluation` evaluates an actual normalized
refined induced function at a supplied ambient product-Levi point. Its source
is the actual normalized induced action restricted to coarse block scalars;
its target is the inducing action restricted along the constructed refined
Levi homomorphism. Right translation by the coarse scalar equals left
translation because that scalar is central in the ambient product Levi. The
actual parabolic section and its projection let the defining covariance apply.
The positive refined half modulus is one at repeated coarse block scalars,
by `refinedLeviHalfModulus_blockScalarLevi_comp`. Thus the target action has
no additional modulus twist. Linearity is pointwise.

`refinedCoarse_eval_mem_characterSpace` applies the public
intertwiner-preservation lemma to this actual map. It preserves the same
character and supplied common finite power at every point.
`normalizedRefinedInduced_coarse_character_reflects` takes a nonzero
vector from a uniform generalized character space, chooses a nonzero function
value by subtype extensionality, and applies the public nonzero-image lemma.
The conclusion is occurrence of that same coarse tuple character on the
actual restriction of the inducing representation.

No irreducibility, smoothness of the inducing action, admissibility, finite
length, finite spectrum, positive rank or character extension is assumed.
The restriction need not be extended to the full fine centre. This does not
prove a conjugation formula for an arbitrary geometric grade or an exponent
projection, whole-induction isolation, or the parent Hom comparison. Its provenance is internal, with no new literature input.

Worker 526 implemented this construction. Workers 359 and 430 supplied
coordinate, normalization and same-power transport guidance during the
parent Hom-comparison investigation. This attribution supplies no analytic
comparison result.
