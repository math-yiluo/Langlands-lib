# The centralizer inside a sectioned quotient kernel

This is internal derived content for the finite-field torus envelope argument.
It constructs no quotient or section: both are supplied explicitly.

`torusCentralizer_eq_comap_of_mono` proves on every relative test scheme that
centralizing a commutative subgroup can be checked after a monomorphic ambient
homomorphism. Its proof applies that homomorphism to a commutation equality in
one direction and cancels its underlying monomorphism in the other.

`TorusKernelCentralizerData s n` stores an actual closed subgroup of the
specified kernel representative `N`, representing exactly
`(torusCentralizer s).comap n` on every relative test scheme. It records
smoothness, affineness, connectedness and unipotence of this same source.

The constructor `torusKernelCentralizerData` assumes a smooth connected affine
ambient group, an affine commutative torus quotient, a closed homomorphic
section, and a closed monomorphic affine, locally finite type, unipotent
representative of the full quotient kernel. The Library's closed centralizer
representability gives `z : Z → G` representing the whole centralizer of the
section. Published torus-centralizer smoothness and connectedness make `Z`
smooth and connected; closedness makes it affine. Commutativity of the torus
lifts the section into `Z`, so `Z → T` has the same section identity. Applying
`SectionedSubgroupKernel` to this map constructs its actual full kernel inside
`N`, with precisely the stated all-test range and geometry. Over a perfect
field the published perfect-field splitness proof supplies a finite represented
split unipotent series for the stored group.

For a monomorphic ambient inclusion `h : H → G`, a restricted kernel
`v : V → H`, and a compatible map `m : V → N`, the intersection lemmas
compare the two actual kernel centralizers. The compatibility equation is
`m ≫ n = v ≫ h`. If `dG` and `dH` represent the centralizers inside `N` and
`V`, respectively, `represents_intersectionFst` shows that the actual
scheme-theoretic intersection of `m` and `dG.inclusion` represents the same
subgroup functor as `dH`. The proof combines the published intersection
representability theorem, composition of subgroup-functor inverse images,
the compatibility equation, and reflection of the whole centralizer through
`h`. Uniqueness of represented subgroups gives `intersectionIso`; its
projection to `V` is exactly `dH.inclusion`.

`intersection_geometry` transports smoothness, affineness, connectedness and
unipotence along that isomorphism to the actual intersection.
`intersection_isSplitUnipotent` then applies the published perfect-field
splitness theorem to this same intersection. These results assume neither a
rational-point product formula nor normality of an envelope.

The construction preserves the original subgroup functors and includes
nonreduced test schemes. It is a supporting geometry unit and does not prove
the final finite-field envelope normality proposition.
