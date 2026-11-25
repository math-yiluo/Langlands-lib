# Star equivariance of character restriction to an anisotropic kernel

This module proves that actual integral character restriction to a kernel
torus intertwines the full absolute star actions. The kernel is any group `D`
with index data `e` and a published `TitsIndexData.KernelComparison` with
the index data `d` of `G`. The restriction map is `KernelComparison.weightRestriction`.
That map precomposes absolute characters with the base change of the
comparison's actual torus morphism.

`aut_pairing_weightEquiv_coroot` is a general identity for an automorphism
`δ` of an integral root pairing. The pairing of `δ.weightEquiv x` with the
coroot at `i` equals the pairing of `x` with the coroot at
`δ.indexEquiv.symm i`. The proof uses the Mathlib transpose identity for
root-pairing equivalences and the coroot formula for their coweight maps.

`pairing_starAction_weight_coroot` specializes this identity to the star
automorphism `(d.pinning.starAction σ).val`. The inverse index permutation
of `starAction σ` is the vertex permutation `d.star σ⁻¹`, because
`starAction` is a group homomorphism.

`KernelComparison.weightRestriction_starAction` assumes that the simple
coroots of `e` span its integral cocharacter lattice. It then proves
`h.weightRestriction (σ ⋆ x) = σ ⋆ h.weightRestriction x` for every
absolute Galois element `σ`. Each side pairs with a simple kernel coroot
`b` as `x` pairs with the ambient coroot at `d.star σ⁻¹ (h.vertexEquiv b)`.
The published `KernelComparison.pairing_weightRestriction_simple` and
`KernelComparison.vertexEquiv_star` give this. The published
`IntegralWeylVector.eq_of_pairing_simple_eq` turns equal simple-coroot
pairings into equality of integral characters.

`KernelComparison.weightRestriction_starFixed` concludes that restriction
carries a weight fixed by every ambient star automorphism to a weight fixed
by every kernel star automorphism.

The coroot-span hypothesis is explicit. For a simply connected kernel the
Library theorem `TitsIndexData.pinning_corootSpan_eq_top` supplies it. The
module `SimplyConnected/AnisotropicKernelStarRestriction` uses this for the
chosen actual anisotropic kernel of a simply connected group. No field characteristic, perfectness,
Cartan type or star triviality is assumed.

The provenance is internal: these identities follow from the published
kernel comparison and Mathlib's root-pairing API. No Tits algebra or Brauer
class is constructed or compared here.
