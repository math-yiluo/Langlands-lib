# The actual identity jet module

Fix a scheme `S` and an actual group scheme `G` over `S`, in any universe.
Write `p : G → S` for its structure morphism and `e : S → G` for its
identity section. The constructions below use these actual morphisms.

`Langlands.GroupScheme.IdentityJet.ideal G n` is the quasi-coherent ideal
sheaf data `(ker e)^(n+1)`. `scheme G n` is its associated closed subscheme,
`inclusion G n` its closed immersion into `G`, and `projection G n` the
composite with `p`. `module G n` is the pushforward along this composite of
the actual structure module of the subscheme. These definitions make sense
without affineness or smoothness assumptions. `quotientMap G n` is the
morphism from the pushforward of the structure module of `G` to this jet
module induced by restriction to the closed subscheme; `quotientMap_app`
computes it as the actual inclusion's pullback on functions.

For any open `U` of `S`, evaluation at `e` defines the algebra homomorphism
`augmentation G U : Γ(G,p⁻¹U) →ₐ[Γ(S,U)] Γ(S,U)`. Its algebra property is
proved from `e ≫ p = id`. The algebra structure on the source, exposed as
`sectionAlgebra G U`, is the one induced by the actual structure morphism
`p.app U`. It is installed only locally in this module; users can install
that explicit algebra structure when using the quotient comparison.

When `p` is separated, the identity section is a closed immersion. The
support of each positive power of its defining ideal is the image of the
section. Thus the projection from the jet to the base is a homeomorphism on
underlying spaces, with inverse given on points by the section. The projection
is affine by the affine-morphism criterion for an inducing map with closed
range. This step applies to any separated ambient group.

Now assume `p` is affine and `U` is an affine open of `S`. Then `p⁻¹U` is
affine, represented by `affineOpen G U`. The section's
scheme-theoretic kernel on `p⁻¹U` is the actual kernel of its map on affine
functions. The equality `e⁻¹p⁻¹U = U` identifies that kernel with the kernel
of `augmentation G U`; `ker_augmentation` and `ideal_apply` record these
identifications and their ideal powers.

Put `R = Γ(S,U)`, `A = Γ(G,p⁻¹U)`, and `I = ker(augmentation G U)`.
The canonical ring isomorphism `sectionsRingEquiv G n U` identifies
`Γ(scheme G n, (projection G n)⁻¹U)` with the actual quotient `A/I^(n+1)`.
It is the standard affine chart isomorphism of the ideal's closed
subscheme followed by the quotient isomorphism induced by `ideal_apply`.
`sectionsRingEquiv_inclusion_app` sends the restriction of a function `a`
on `p⁻¹U` to its actual quotient class. The analogous formula for the
projection identifies the base algebra maps.

The linear isomorphism `sectionsEquiv G n U` has the same underlying map:

`Γ(module G n,U) ≃ₗ[R] Algebra.SectionJet.Quotient (augmentation G U) n`.

Its linearity is proved for the actual pushforward module action: the
scalar `r` acts by multiplication by `(projection G n).app U r`, whose
image under the ring isomorphism is the quotient's algebra map of `r`.
`sectionsEquiv_inclusion_app` and `sectionsEquiv_quotientMap` preserve the
formula sending actual restricted functions to quotient classes. Thus the
comparison retains the specified restriction map, rather than only the
isomorphism class of the section module.

If `p` is also smooth, its map on these affine sections makes `A` a smooth
`R`-algebra. The instances `finite_sections` and `projective_sections`
transport the section-jet finite-projectivity theorem across
`sectionsEquiv`. Hence the actual jet module has finite projective
sections over every affine open of the base, over arbitrary commutative
base rings and without a noetherian hypothesis.

This is an internal supporting construction for the parabolic jet
polarization argument. Its provenance is the actual identity section,
Mathlib's ideal-sheaf subschemes and pushforward structure modules, and
the section-jet algebra results in `SectionJetFiltration`. It does not yet
construct sheaf local bases, identify higher layers with symmetric powers,
compare determinants, or prove ampleness.
