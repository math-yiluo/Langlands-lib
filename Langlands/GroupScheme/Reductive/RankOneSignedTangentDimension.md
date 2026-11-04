# Signed tangent dimensions of an integral rank-one symmetrization

This internal derived helper transports the actual tangent submodule of a
subgroup functor through an actual group-scheme isomorphism. It specializes
that transport to the integral cocharacter `ν - wν` and deduces conditional
positive-root uniqueness for the original `ν`. All results retain an arbitrary
field `k : Type u` and apply in every characteristic.

`RelativeRoot.tangentSubmodule_comap` identifies the tangent submodule of an
inverse-image subgroup with the inverse image under `Lie.targetMapLinear`.
The equality is definitional: both sides test the image of an actual
identity-kernel dual-number point for membership in the subgroup functor.
`RelativeRoot.tangentSubmoduleEquivOfComap` restricts the published
`lieKernelLinearEquiv` using `LinearEquiv.ofSubmodule'`. Its underlying map
is the actual differential of the group-scheme isomorphism, as recorded by
`tangentSubmoduleEquivOfComap_apply`. The resulting
`finrank_tangentSubmodule_comap_iso` requires no finite-dimensionality premise.
These generic results require affine source and target group schemes, but no
representability of the subgroup functor.

For a connected reductive group and a split maximal torus whose actual roots
are pairwise integrally dependent,
`IsConnectedReductive.normalizerSymmetrizedUnipotentTangentEquiv` gives a linear
equivalence between the actual tangent submodules of `U(η)` and `U(-η)`, where
`η = normalizerSymmetrizedCocharacter i n ν = ν - wν` for a supplied normalizer
point `n`. The published exact all-test conjugacy
`unipotent_normalizerSymmetrizedCocharacter_conj` identifies `U(η)` with the
inverse image of `U(-η)` under conjugation by `n`. The implementation first
uses this equality and then the generic restricted tangent equivalence.
`IsConnectedReductive.finrank_tangentSubmodule_unipotent_normalizerSymmetrized_eq_neg`
is the resulting dimension equality. Neither result requires the class of
`n` to be nonidentity.

`IsConnectedReductive.positive_roots_eq_of_normalizerSymmetrized_unipotent_finrank_le_one`
retains a nonidentity class of `n` in the actual quotient `N(k)/Z(k)` and a bound
of one on the tangent dimension of `U(η)`. The published integral pairing
doubling theorem makes every root positive for `ν` positive for `η`.
`RelativeRoot.positive_roots_eq_of_tangentSubmodule_unipotent_finrank_le_one`
then proves equality of any two roots positive for the original cocharacter.
Reductive smoothness supplies local finite type for that final implication.
The signed variant
`IsConnectedReductive.positive_roots_eq_of_signed_normalizerSymmetrized_unipotent_finrank_le_one`
accepts the dimension bound for either `U(η)` or `U(-η)`, converting the second
case by the signed dimension equality. Pairing doubling takes place in the
integers and uses no division, including in characteristic two.

The provenance is internal: the module combines published exact dynamic
conjugacy, actual Lie-kernel transport, integer pairing doubling, and the
published positive-root tangent-dimension criterion with standard submodule
linear algebra. Worker 1547 proposed the signed-dimension and original-root
bridge; Worker 1549 implemented it. This helper does not produce a nonidentity
Weyl class or prove either dimension bound. It does not prove the unconditional
`RankOnePositiveRootUniquenessStatement`; the remaining geometric inputs must
still be established separately.
