# Unipotent kernels of restrictions to parabolic subgroups

This internal unit composes the Library's normal-unipotent Borel containment,
fpqc descent of all-test subgroup containment, represented subgroup factors,
actual kernel comparisons, and unipotent extension theorem. It is a prerequisite
for the radical-preimage comparison of supplied Bruhat–Tits model maps.

For a smooth connected affine group over any field, `IsParabolicSubgroup.radical_le`
places any supplied represented ground-field unipotent radical in every
parabolic subgroup. The proof extends the field to its algebraic closure,
chooses the geometric Borel furnished by parabolicity, applies normal-unipotent
Borel containment, and descends the resulting containment on every scheme test.
It only uses the radical's smoothness, connectedness, unipotence and normality;
it does not assume that ground-field radical maximality survives base change.

`IsParabolicSubgroup.radicalFactor` is the homomorphism from the actual supplied
radical to the actual supplied parabolic. Its composite with the original
parabolic inclusion is the original radical inclusion. If that radical is the
full kernel of a supplied quotient, its factor represents the full kernel of
the quotient restricted to the parabolic. The actual kernel is consequently
smooth, connected and unipotent.

The other helpers remove monomorphic postcomposition from the actual kernel
property and compose homomorphisms with smooth connected unipotent kernels.
The monomorphic-postcomposition step reuses the published
`Langlands.GroupScheme.range_kernelι_comp_mono` from
`GroupScheme.Absolute.TriangularDiagonalImageReduction`.
The composition result assumes that the first homomorphism is flat,
scheme-surjective and locally of finite presentation, and that all three
groups are affine. Its kernel is the actual inverse image of the second
kernel. Smoothness follows from the first map's smooth kernel, connectedness
from its geometrically connected kernel, and unipotence from the published
unipotent extension theorem. All kernel comparisons concern full subgroup
functors on every relative scheme test.

This unit proves structural helpers only. It does not assert the complete
facet comparison or the maximal pro-p proposition.
