# Cartesian restriction to represented subgroup functors

This internal geometric lemma concerns actual group schemes over an arbitrary
scheme `B`. Let `i : H → G` and `j : K → Q` represent subgroup functors `F`
and `E`. No smoothness, connectedness, affineness or centrality is required.

`IsRepresentedBy.mapPointsHom` sends points of `F` through an actual ambient
homomorphism `q` when `F ≤ E.comap q`. `IsRepresentedBy.restrictionHom`
uses these natural monoid homomorphisms and Yoneda lifting to construct the
actual induced homomorphism `H → K` between the supplied representatives.
`restrictionHom_comp` proves that it commutes with the two inclusions.
These constructions need only containment, rather than equality, of functors.

`IsRepresentedBy.isPullback_of_comap_eq` assumes a commuting square
`i ≫ q = p ≫ j` and the all-test equality `E.comap q = F`. It proves that
the square of schemes over `B` is cartesian. A pair of compatible test points
has its first component in `F`; representability gives its unique lift to `H`.
Monicity of `j` checks the second component, and monicity of `i` proves
uniqueness.

`IsRepresentedBy.isFppfImage_of_comap_eq` additionally assumes that the actual
scheme morphism underlying `q` is flat, surjective and locally of finite
presentation. It uses the constructed `restrictionHom` as `p`. The preceding cartesian square shows that `p`
inherits those three properties by base change. Thus `IsFppfImage F E q`
holds for the supplied subgroup representatives. The proof does not infer
surjectivity over each original test scheme.

`comap_eq_iff_isFppfImage_and_kernel_le` combines this construction with the
published converse in `SubgroupFunctor.FppfImage`. For represented `F`, `E`
and an fppf `q`, the equality `E.comap q = F` is equivalent to an actual
fppf image together with containment of the full kernel range in `F`.
Kernel containment in the forward direction follows by sending a kernel
point to the identity in `E`.

These are internal deductions from all-test representability, Yoneda lifting,
base change of the three morphism properties, and the existing fppf membership
descent theorem. They remain valid for a nonsmooth kernel. They supply no
semigroup comparison or inverse-image equality by themselves.
