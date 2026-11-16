# A centre-moving automorphism of the actual E-type anisotropic kernel

`RankOneTypeEKernelCenterMovementStatement` is an unproved geometric
prerequisite over every field `k : Type u`. The group scheme is affine and of
locally finite type, and `d` is an actual `TitsIndexData G`. The statement assumes
that `G` is simply connected, absolutely almost simple, and of split rank one,
and that the entire absolute Galois star action of `d` fixes every simple vertex.

There are two alternatives for an exact numbering of the entire actual vertex
type. They compare every ordered integral Cartan entry with `E 6` or `E 7`,
respectively, and require the distinguished subset to be exactly zero-based
vertex 1. This is Mathlib's branch vertex; deleting it gives the ordered A5 or
A6 chain. No type label or freely supplied kernel is substituted for the
actual matrix, marking, star action, or anisotropic kernel.

The requested conclusion is `HasCenterMovingAutomorphism` of
`d.anisotropicKernelIndex.kernel`, the particular actual derived centralizer
kernel furnished by the published index interface. It asks for an actual
group-scheme automorphism and failure of full-centre fixation on all test
schemes. The conclusion does not ask for a supplied root-datum action,
an algebra anti-equivalence, or an involutive automorphism.

The provenance is internal: this target isolates the missing geometric step
between the actual rank-one index and the full-centre automorphism interface.
The intended route uses a rational relative-Weyl representative acting on the
actual derived centralizer, followed by the actual absolute-root comparison.
That route is not implemented here. In particular, the conclusion is not
inferred merely from a symmetry of a diagram.

There is no local-field, field-characteristic, residue-characteristic or
universe restriction. The accompanying local obstruction file proves only
conditional consequences, retaining both this target and the separate
`NormOneCenterAutomorphismOppositeStatement` as explicit premises. Neither
geometric centre movement nor the local rank-one enumeration is proved here.
