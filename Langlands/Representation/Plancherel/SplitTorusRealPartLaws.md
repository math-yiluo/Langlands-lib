# Intrinsic laws of the actual split-torus real parameter

This derived companion works with the same arbitrary-universe local fields,
actual split tori, positive valuation and real lattice pairing as the construction.
It adds choice independence, naturality and comparison with the existing
normalized real functional on the actual integer valuation image.

`normalizedRealPartFromLift` performs the logarithm-and-scalar-extension
construction with an arbitrary multiplicative lift of the cocharacter lattice.
For a smooth character, any lift whose valuation is the embedded cocharacter
gives the original normalized parameter. The proof evaluates the proved
all-point logarithmic formula on the lift and uses pure-tensor extensionality.
The lift's valuation normalization is a condition on that lift, rather than a
norm formula or existence assumption about the character.

Every field unit of positive order one has the same cocharacter valuation.
This follows from the intrinsic character–cocharacter power formula and the
existing integer valuation characterization. Consequently evaluating the
logarithmic modulus at any order-one uniformizer gives exactly `sectionLog`.
Values on any integral basis determine the same parameter: scalar extension
of that basis and the perfect pairing prove the equality. Thus neither a
uniformizer nor a lattice basis changes the constructed parameter.

The positive valuation is natural under actual morphisms of split tori,
through the published real cocharacter map. The proof uses integer-character
valuation naturality and the published pairing naturality. The all-point
norm formula and uniqueness then identify the real part of a point-character
pullback with the published real character restriction of its real part.
Continuity of the actual point map proves that this pullback remains smooth
for the canonical rational-point topology. The same naturality holds for
the raw parameter by its exact scalar relation. In particular any splitting
isomorphism computes the same intrinsic result.

For an existing actual-image character, its pullback has open kernel because
it is trivial on the published open common norm kernel. Evaluating the
normalized real parameter at an actual valuation vector is then exactly the
existing `rationalImageRealPart` at the actual image projection. This follows
by unfolding the two normalized logarithms, with no replacement of the image
or point topology.

Finally, the existing empty-coordinate real-space equivalence gives an
explicit rank-zero specialization: the normalized and raw parameters are
zero for every character, without a smoothness premise. All other results
also allow rank zero. The raw logarithm remains `(-log q)` times the
normalized exponential parameter throughout.
