# Signed height of an invertible tensor over an arbitrary affine base

`ModuleLaw.QuasiIsogeny.scalarIsogenyPresentationOverRing` chooses an actual
integral isogeny numerator for an invertible tensor between uniformizer-divisible
coordinate laws. Clear a uniformizer power in each of the inverse tensors. The
injectivity of integral Hom in tensor Hom identifies the two integral
composites with the corresponding scalar powers. The arbitrary-ring scalar
composites theorem then gives the finite locally free kernel and local
surjectivity of the chosen numerator.

`ModuleLaw.QuasiIsogeny.toLocalQuasiIsogeny` sends the tensor to its actual
rational section with the resulting local isogeny witnesses. For a finite
residue field and finite scalar heights at both ends, `heightFunction`
selects the unique signed kernel-rank height on the affine spectrum.
`hasHeightFunction` verifies the local rank presentations and
`heightFunction_eq` identifies any other verified function with this one.
The coefficient-change and integral-coordinate comparison lemmas apply
these uniqueness and existence results to the transported presentations.

This is derived infrastructure for measuring the actual affine rigidifier
of Harris 1997, Appendix, printed pp. 112–113, and for the chart heights in
the split comparison of Rapoport–Zink, Lemma 6.44, printed pp. 309–310.
