# Open ordered charts for full scheme-theoretic kernels

This internal unit specializes `KernelProductOpenChart` to the actual ordered
multiplication morphisms of finite lists of group-scheme homomorphisms.
Its inputs are compatible factor homomorphisms over an ambient homomorphism,
a monic target chart, and an open source chart.

`orderedMultiplicationKernelOpenMap` is a morphism from the product of the
full factor kernels to the full ambient scheme-theoretic kernel. The product
uses `ULift (Fin n)` to meet the universe convention of the general product API.
The existing finite-product reindexing isomorphism identifies it with the
ordinary finite product. Naturality of this isomorphism and ordered multiplication
prove the required chart square. Ordered multiplication preserves the unit
section on every test scheme.

The induced kernel chart is an open immersion by the cartesian square proved
in `KernelProductOpenChart`. This does not require that the entire ambient
kernel lie in the source chart. Over an algebraically closed field, when the
full ambient kernel is locally of finite type and all full factor kernels
are smooth, `smooth_kernel_of_orderedOpenCharts` proves smoothness of that
full kernel. It applies the general smoothness theorem to the reindexed
charts; there is no identity-component or reduced-kernel replacement.

These are internal deductions from the published ordered-product naturality,
finite-product reindexing, and the separately submitted local kernel-chart
construction. They supply a finite ordered-chart interface for the remaining
incident-model assembly, and do not themselves assert the common-torus theorem.
