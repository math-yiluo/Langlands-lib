# Compact-open inclusion from the actual rational norm kernel

Author: Worker 485.

This internal adapter constructs `rationalNormKernelAmbientLevel G K`, the image
of an open subgroup K of the actual common rational-character norm kernel under
its actual inclusion in `GroupScheme.rationalPoints G`. It addresses the level
comparison needed when applying the ambient support argument in Renard VI.3.4,
printed pp.145–146 / PDF pp.151–152, French edition dated 9 July 2026, and VI.2.4,
printed p.141 / PDF p.147. The registered original is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The construction and its comparison laws are internal deductions from the
published openness of the actual norm kernel; they are not separately numbered
assertions in the source.

F is an arbitrary nonarchimedean local field. The group scheme G is affine and
locally of finite type. These premises are weaker than connected reductivity
and retain arbitrary characteristic, rank zero and empty root systems. The
ambient point group carries exactly `rationalPointTopology F G.X`; its norm
kernel carries the inherited subgroup topology. The coefficient ring R, field F
and module V have independent universes. The algebraic action on V needs no
smoothness, admissibility, irreducibility or dimension premise.

The constructed ambient subgroup is `K.toSubgroup.map H.subtype`, where H is the
published `rationalCommonNormKernel G`. The theorem
`isOpen_rationalCommonNormKernel G` makes the subtype inclusion an open map, so
the image of the open set K is open in the ambient group. The underlying set is
exactly the image under `Subtype.val`, recorded by
`rationalNormKernelAmbientLevel_coe`. If K is compact, continuity of the same
subtype inclusion proves compactness of this image in
`isCompact_rationalNormKernelAmbientLevel`. Thus the construction transports the
given compact open level itself, without selecting a smaller subgroup.

`rationalNormKernelAmbientLevel_le` records containment in H.
`rationalNormKernelAmbientLevel_comap` proves that pulling the image back through
the actual inclusion recovers exactly K, using injectivity of `Subtype.val`.
The published `fixedVectors_comp_subtype` then proves
`fixedVectors_rationalNormKernelAmbientLevel`: fixed vectors for the restricted
action at K are exactly fixed vectors for the ambient action at its image.
`dualInvariant_rationalNormKernelAmbientLevel_iff` proves the corresponding
invariance equivalence for any algebraic functional by the explicit image
witnesses. `inverseCoefficient_rationalNormKernel_restrict` records that the
inverse coefficient is evaluation of the same action and functional after the
actual inclusion; subgroup inversion agrees with ambient inversion.

The imported `RationalNormKernelSmoothDual` already identifies the entire smooth
dual of an ambient action restricted to H with the ambient smooth dual. This
adapter reuses that published comparison and does not introduce a selected-dual
notion. These results do not extend an arbitrary irreducible H-representation to
an ambient irreducible, nor provide a common support bound. Those remain
separate obligations in the uniform-support proof. No fixed-level finiteness,
restriction-constituent finiteness or category decomposition is proved here.
