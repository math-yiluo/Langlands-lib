# Localization of an average over a compact subgroup

`CompactSubgroupPowerLocalizationStatement` uses a continuous group
homomorphism from a compact group \(H\) to a compact group \(K\) and
a continuous real weight \(p\) on \(K\), with values in \([0,1]\).
Both groups are Hausdorff and second countable and carry their Borel
measurable structures.
The weight is one exactly on the image of \(H\) and is invariant under
left multiplication by that image. Nonnegative integrals of \(p^m f\)
over \(K\) imply a nonnegative integral of \(f\) over \(H\).
The measure on \(K\) is finite, left invariant and positive on nonempty
opens. The measure on \(H\) is a right invariant probability measure.

The proof replaces \(f(k)\) by its continuous left average
\(\int_H f(hk)\,dh\). Right invariance of the measure on \(H\) makes this
average constant on the image subgroup. Fubini and left invariance on \(K\)
show that averaging preserves every weighted integral. The Library's
`compactPowerLocalization` detects the sign of this average at the identity.

This is a derived measure-theoretic step for the compact form in real
parabolic induction.
