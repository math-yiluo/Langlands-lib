# Successive represented root-height kernels

Worker 204, Task 7200. This internal derived unit assumes the arbitrary-ring
`RootHeightChart` interface and completes the kernel comparison for its
represented height terms. It makes no claim that such a chart exists for
every relative radical or that local constructions descend.

`step d` is the actual group-scheme morphism from height `d + 1` to height
`d`. The Library's represented-subgroup point equivalences transport
the inclusion of the all-test point subgroups to `stepPoints`. Cancellation
by the current inclusion proves naturality, and the group-valued Yoneda
construction gives `step`. `step_comp_inclusion`
identifies its composite into the original group. Cancellation by the
monomorphic original inclusion then shows that the range of `step d`
consists exactly of points whose ambient image belongs to height `d + 1`.
Closedness follows from the two original closed immersions. Normality
follows by pulling back the already proved ambient normality through the
current inclusion. The source of each step is smooth by
`RootHeightFiltration.smooth_groupScheme`.

For `0 < d`, `quotientMap_eq_one_iff` compares the exact-height quotient
with that same next subgroup on every scheme test. A point in height `d`
already has zero coordinates below `d`. Its quotient is the identity
precisely when all coordinates of height exactly `d` vanish: the quotient
coordinate formula and the bijective exact-height enumeration prove this,
including empty layers. Together these conditions say exactly that the
ambient coordinates below `d + 1` vanish. The subgroup membership theorem
then gives the required equivalence.

`range_kernelι_quotientMap` applies the Library's all-test characterization
of the actual scheme-theoretic kernel and the range criterion for `step`.
`isFppfQuotient_quotientMap` combines this exact kernel equality with the
flatness, scheme surjectivity and local finite presentation established in
`RootHeightQuotient`. No surjectivity on the point group of every test is
assumed. All rings and all scheme tests at arbitrary universe `u` are
retained. The provenance is the represented-subgroup lifting API, the
supported-coordinate description, and the preceding quotient geometry;
no additional literature result is used.
