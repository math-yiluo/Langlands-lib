# The represented ground-field radical quotient

`unipotentRadicalQuotient` proves the exact
`UnipotentRadicalQuotientStatement` over an arbitrary field at universe `u`.
It takes the supplied represented ground-field unipotent radical. The actual
smooth normal quotient constructor gives the quotient group scheme and its
group-scheme projection, including the exact represented fppf kernel.

The source has an actual finite-dimensional representation with the given
closed normal unipotent subgroup as its full kernel. It descends through the
fpqc projection to a faithful representation of the quotient, using all
relative scheme tests. The affine-model construction identifies this quotient
with the smooth closed affine generated image of the source representation.
Thus the original quotient is affine. Smoothness is included in the quotient
construction, and its continuous surjective projection transfers connectedness.

The helper `IsUnipotentRadical.hasTrivialUnipotentRadical_of_smooth_quotient`
proves triviality of the ground-field unipotent radical of an actual
smooth, scheme-surjective, quasi-compact quotient with exactly the
all-test kernel represented by the supplied radical.

The kernel is compared with that representative to transfer affineness,
unipotence, and geometric connectedness. For any smooth connected unipotent
normal closed subgroup of the quotient, take its actual preimage. Smoothness
and geometric connectedness of the quotient map give smoothness and connectedness
of the preimage. Its inclusion in the affine source makes it affine.
The full kernel of the preimage projection is canonically the original
full kernel. The unipotent-extension theorem therefore makes the preimage
unipotent. Maximality of the supplied radical and the published all-test
preimage reduction imply triviality of the original quotient subgroup.

These constructions preserve the actual quotient scheme and map throughout.
No perfectness, splitting, geometric reductivity or surjectivity on rational-point
groups is used. The internal proof combines the published actual homogeneous
quotient, descended group structure, represented-kernel comparison,
preimage geometry, coefficient-representation and affine-model constructions.
