# Standard cocharacters annihilating ambient rational characters

Worker 1555 derives an integral cocharacter construction from the published
actual relative Weyl action. This is an internal construction for the compact
restriction converse; it does not assert that the converse is proved.

For a split torus morphism `i` with finite actual relative Weyl group `W`,
`normKernelCocharacter i ζ` is `card(W) • ζ` minus the sum of all Weyl
translates of `ζ`. The construction uses no division and works in every
field characteristic.

The module reuses `normKernelCocharacter` and the restricted-character
pairing theorem from `NormKernelCocharacter`. That shared module uses the
published Weyl invariance and moves the action across the integral lattice
pairing to show that every restricted ambient character pairs to zero
with the correction.
The published `latticePairing_relativeWeylCocharacterSum_eq_zero`, using
the given actual relative root system's reflections, shows that each root
pairing is multiplied by `card(W)`. Since the group has an identity,
this cardinality is positive. Therefore the correction of a standard
cocharacter remains standard for the same simple-root face.

The root-pairing and standard-face declarations in this module are
`latticePairing_normKernelCocharacter_root_of_relativeRootSystem` and
`IsStandardCocharacter.normKernelCocharacter_of_relativeRootSystem`.
They retain the actual-root-system hypotheses, while the shared module
also provides versions with explicit root-reflection hypotheses.

The primary construction requires a finite actual Weyl-group enumeration.
The root-pairing and standard-face theorems additionally retain splitness,
the actual relative root system, and the stated affine and monomorphism
instances. The module itself asserts no topological compact escape, no
Iwahori basis, and no representation-theoretic conclusion. Its provenance
is the integral Weyl-sum argument implemented above, using
`WeylPositiveCocharacter` and `RelativeWeylRootKernel`.
