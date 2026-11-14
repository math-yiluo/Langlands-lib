# Local cocycle triviality for extensions of split tori

This internal interface combines the published split-torus local cocycle theorem
with affine kernel cocycle vanishing. Its hypotheses describe actual group
schemes and maps over the spectrum of an arbitrary commutative ring. It asserts
no existence theorem for a Borel subgroup or a vector-quotient series.

`Cocycle.IsZariskiLocallyTrivial` means that at every base point the cocycle has
a `LocalTrivialization`: one actual open neighbourhood, a group-valued cochain
on the inverse image of that open in the cover, and the coboundary identity on
every test scheme over the original base.

`SplitSolvableLocalCocycle.isZariskiLocallyTrivial_of_section` concerns
`K → H → T`. The first map is monomorphic, its all-test image equals the kernel
of the second map, and the second map has a section as a scheme map over the
base. The kernel satisfies `SplitUnipotentAffineTorsor.CocyclesVanish`, and `T`
is a split torus. Every `H`-valued cocycle on an affine flat surjective cover
of the base is then Zariski locally trivial.

The proof first trivializes the quotient cocycle near the chosen base point,
using `Cocycle.nonempty_localTrivialization_of_isSplitTorus`. It chooses an
affine open inside this neighbourhood and restricts the cover and quotient
cochain to it. Composing the quotient cochain with the scheme section lifts
it to `H`; twisting by this lift makes the cocycle valued in the kernel.
The all-test kernel-image equality and monomorphy yield a `K`-valued cocycle.
Its restriction to the affine open is trivial by `CocyclesVanish`.
`Cocycle.IsTrivial.of_baseChangeAlong` reflects this triviality back to tests
over the original base, since the open inclusion is monomorphic. The
published lifting and twisting lemmas recover the required cochain for `H`.

`isZariskiLocallyTrivial` obtains the scheme section from the published
`SplitUnipotentAffineTorsor.exists_section` when `H` and `T` have affine
underlying schemes and the quotient map is flat, surjective and locally
finitely presented. `isZariskiLocallyTrivial_of_vectorSeries` supplies the
kernel's cocycle vanishing using `HasAffineVectorSeries.cocyclesVanish`;
it additionally assumes that the kernel is affine over the base and has the
specified finite vector-quotient series.

All results allow disconnected bases, the zero ring, and every universe.
The argument is derived from the imported cocycle and affine vanishing APIs,
and introduces no external mathematical input.
