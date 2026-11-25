# The smooth universal family of maximal tori

This internal construction restricts the published smooth universal family of
all closed relative-torus subgroups of a reductive group to its actual open
maximal locus. The base scheme and universe are arbitrary. The result
`exists_smooth_isUniversalMaximal` supplies a commutative group-scheme family,
its closed inclusion, the relative-torus property, residue-fibre maximality,
the universal property on every test scheme, and smoothness of the parameter
map. Surjectivity and quasi-affineness are separate obligations.

The open subset `TorusSubgroupModuli.maximalOpen` is the actual maximal locus
of the supplied family in the reductive ambient group pulled to the parameter
scheme. The arbitrary base-change equality for that locus identifies fibrewise
maximality of a pulled-back inclusion with containment of the image of the
base map in the original maximal locus. Family evaluation also includes the
canonical isomorphism from the iterated ambient pullback to the specified
ambient group. On every residue fibre, ambient-isomorphism invariance of
maximality removes this comparison. Thus the same image-containment condition
characterizes maximality of the actual evaluated family on every test scheme.

For existence, apply smooth torus-subgroup representability, equip its actual
relative-torus family with the descended commutativity proof, and form the
open maximal locus. The commutative adapter retains the underlying group
scheme and inclusion. The proved open-restriction universal property now
applies using the all-test characterization just established. Closedness and
the relative-torus condition persist under pullback to the open subscheme,
and the composite of its open immersion with the smooth original parameter
map is smooth.

All inputs are published constructions or the separate internal
maximal-locus, commutativity and open-restriction modules. The construction adds
no geometric premise and does not assume maximal-torus representability.
