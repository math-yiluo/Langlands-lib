# Global cocycles for extensions with a WeilGm quotient

This internal helper proves global cocycle vanishing for a supplied affine
extension over a semi-local ring, or under the corresponding Picard hypothesis.
All schemes and rings are in an arbitrary universe `u`.

`Cocycle.isTrivial_of_extension_section` first works over any scheme `S` and
with any test object `U` over `S`, without a cover hypothesis. The actual group
homomorphisms `j : K → H` and `q : H → T` satisfy equality of the image of `j`
with the kernel subgroup functor of `q`; the underlying map of `j` is monic.
The assumptions supply a section of `q` as a morphism of schemes over `S`,
vanishing of every `K`-cocycle on this same `U`, and triviality of the image
of the given `H`-cocycle in `T`. The conclusion is triviality of the original
cocycle on `U` in the published all-test sense.

The proof chooses a quotient cochain and composes it with the scheme section.
Twisting by this lifted point makes the quotient value equal to one for every
pair of points over every test scheme. The kernel-image equality then lifts
the twisted cocycle through the monomorphism `j`. Kernel vanishing trivializes
this lifted cocycle. The published `IsTrivial.of_lift` and `of_twist` transport
that cochain back to the original cocycle. The scheme section need not be a
group homomorphism.

For the remaining theorems the base is `Spec A`, `H` and `T` are affine,
and the underlying map of `q` is flat, surjective and locally finitely
presented. The kernel satisfies `SplitUnipotentAffineTorsor.CocyclesVanish K`,
which quantifies over all affine base changes and affine flat surjective
covers. The supplied isomorphism `e : T ≅ WeilGm.groupScheme A B` has a
module-finite projective coefficient algebra `B/A`. The cover `U → Spec A`
is flat, surjective and locally finitely presented; its total space need not
be affine or quasi-compact.

`isTrivial_of_weilExtension_fppf_of_pic_trivial` assumes a subsingleton
`CommRing.Pic B`. The published quotient-section theorem constructs a scheme
section of `q` from kernel vanishing. `AffineCocycleFppf` extends kernel
vanishing to the original `U`, and `PicardTrivialFppfCocycle` trivializes the
quotient cocycle on that same cover. The general extension argument applies.
`weilExtensionFppfPicardCochain` chooses the resulting actual morphism
`U → H`; its specification is

`ξ(a,b) = (a ≫ f) * (b ≫ f)⁻¹`

for every scheme test `Z` over `Spec A` and every `a,b : Z → U`.

`isTrivial_of_weilExtension_fppf_of_finiteAlgebrasHaveTrivialPicard` obtains
the coefficient Picard instance by evaluating the finite-algebra Picard
predicate at `B`. Its semi-local corollary uses
`finiteAlgebrasHaveTrivialPicard_of_semilocal`, under
`Finite (MaximalSpectrum A)`. The two `vectorSeries` corollaries supply kernel
vanishing from a finite `HasAffineVectorSeries` and an affine kernel structure
map. This is a series with actual represented vector-group quotients, not a
series inferred from a geometric unipotence condition.

The provenance is internal. The proof combines the published kernel lifting,
quotient-section and twisting constructions with the affine-fppf refinement
and Weil-presentation Picard vanishing helpers. It constructs no Borel subgroup,
no special quasi-split model, no quotient presentation from a torus predicate,
and no vector-bundle filtration. Those geometric inputs remain necessary for
the unchanged reductive quasi-split inner-form target.
