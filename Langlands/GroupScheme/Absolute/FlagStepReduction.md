# Conditional flag-step assembly

This internal construction connects the precise remaining geometric inputs to
`UnipotentTorusBorelsToAllBorelsStatement` at arbitrary universe. It assumes
`SomeBorelQuotientProperStatement`, `FlagInvariantAffineOpenCoverStatement`,
`BorelConjugacyStatement`, and the explicit generic fixedness assertion for a
smooth connected affine unipotent group acting on a proper scheme with invariant
affine neighbourhoods of every rational point. No reducedness of the proper
scheme is assumed. The generic assertion is an explicit higher-order hypothesis. It can be
instantiated by a proof of the corresponding generic fixedness interface.

`factorThroughBorelOfFlagInputs` constructs an actual factor of the subgroup
inclusion through any Borel. Choose one Borel with proper quotients, use the
published smooth-subgroup quotient existence theorem, and equip its actual
quotient with the descended categorical action. The cover input supplies
invariant affine opens for the restricted action; generic fixedness then makes
every rational coset all-test fixed. The one-quotient fixedness adapter combines
this with conjugacy to construct the required factor. The companion theorem
applies the range-of-a-factor lemma to obtain precisely the flag-step
conclusion. All four geometric assertions remain explicit inputs, so this is
not an unconditional proof of the parent target.

Provenance is internal composition of the named Library interfaces and quotient
constructions, developed by Worker 1489 using the generic fixedness scope
communicated by Worker 1460. The ambient group remains an arbitrary smooth
connected affine group; reductivity and normalization of the unipotent subgroup
by the torus are not added.
