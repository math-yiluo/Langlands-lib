# Concrete multiplicative and rectangular measures

Worker 31 constructs the representation-side measures used before quotient
disintegration. Independent review and publication of this pair are required.

The original conventions are JPSS, *Rankin–Selberg Convolutions* (1983),
printed page 376, notation preceding (7), and page 387, §2.4: the multiplicative
group carries Haar measure, the integral compact subgroup is `GL_r(O_F)`, and
the unequal-rank integration variable is an actual rectangular matrix.
Both original pages were read directly. Source `jpss-1983-rankin-selberg`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Unit mass on the specified compact-open integral subgroup is an explicit
normalization chosen here; it is not asserted to be forced by that notation.

The generic compact-open constructor applies Mathlib's actual `haarMeasure`
to a compact set with nonempty interior. The identity witnesses nonempty
interior. The resulting measure is proved Haar, regular, and of mass one on
that subgroup; the local-field multiplicative measure carries the Haar and
regularity instances directly. For the multiplicative group the subgroup is the image of
`O_F`'s units in the field's units. Membership means that both the element and
its inverse are integral. Openness follows from the two continuous coordinate
maps; compactness follows from compactness of the integral unit group.

For the general linear group, the construction imports Worker 43's actual
compact-open level-zero group. Its proved identification with the integral
matrix group gives the normalization `vol(GL_r(O_F)) = 1`, including rank one.
For the actual upper-unipotent group, the inverse image of that integral group
is open and compact. Compactness uses the group owner's proved closed embedding
of the upper-unipotent subgroup. This supplies an actual regular left Haar
measure with integral unipotents of mass one. The module does not claim right
invariance, derive unimodularity, or identify this measure with a chosen scale
of additive matrix coordinates.

`rectangularMeasure` is the finite iterated product of the shared
`HarmonicAnalysis.AdditiveHaarMeasure.measure`. Under the explicit sigma-finite
input and measurable-addition hypotheses, it is proved an additive Haar
measure. The scalar normalization is preserved entrywise. It neither introduces
another additive-character/measure primitive nor chooses a new self-dual scale.
The measurable structure on rectangular matrices is Mathlib's
`Matrix.instMeasurableSpace` from `Mathlib.Analysis.Matrix.MeasurableSpace`,
which is the finite iterated product structure; no project instance is added,
so Mathlib's matrix measurability and Borel API applies to this domain. In zero rows, the measure is proved to be unit Dirac mass at the
unique matrix, as the corank-one specialization of the general JPSS integral
requires.

No measure on the nonnormal space `N_r \ GL_r` is constructed by this file.
In particular the direct image of ambient Haar under the quotient map is not
used as a substitute for disintegration. Quotient existence, its normalization
relative to unipotent Haar, and the Weil integration formula remain explicit
prerequisites. Convergence and local-factor constructions remain unfinished.

The group and field universes are explicit. Measurable structures on the groups
are supplied with their Borel compatibility; the local-field construction uses
the project's nonarchimedean-local-field class. Rectangular additive measures
are defined on Mathlib's matrix measurable structure, and their Haar proofs
state sigma-finiteness and measurable addition explicitly.

The shared `Langlands.HarmonicAnalysis.Basic`, Worker 43's
`Langlands.Representation.Conductor.Congruence`, and Worker 6's
`Langlands.Group.GL.UpperUnipotent` are published Library imports.
Their published sources match those used for native compilation.
No implementation from those pairs is republished here. Pinned Mathlib
`5ed2965256430c3649e86755f9576b54eca72435` supplies the Haar construction,
compactness of units, finite-product Haar instances, and the matrix measurable
structure (`Mathlib.Analysis.Matrix.MeasurableSpace`); their relevant source
definitions and hypotheses were inspected before implementation.
The native build completed without diagnostics; it is development evidence,
separate from independent mathematical review.
