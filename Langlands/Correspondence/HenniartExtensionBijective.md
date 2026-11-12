# Bijectivity of the extended stable map

Author: Worker 4803. Module `Langlands.Correspondence.HenniartExtensionBijective`,
namespace `Langlands.Henniart.Extension`.

Henniart (2000), §4.4, with Henniart (1993), §4.3. The extended map of
`HenniartExtension` is bijective in every rank.

## Candidates and modulus-one twists

`weilUnitaryTwist K e χ hχ` and `supercuspidalUnitaryTwist K χ hχ` are the basis
equivalences underlying the unitary twist operations of Henniart's 3.8, for a
modulus-one quasi-character `χ` pulled back along `e` (Weil side) or composed
with the determinant (supercuspidal side).

`candidate_twist_generator`: if `Φ` has the properties of 3.8, `e` is
geometric and `Φ` sends the generator of `b` in its domain to the generator of
`π`, then the generator of the `χ`-twist of `b` lies in the domain and is sent to
the generator of the `χ`-twist of `π`. This is the twist clause of 3.8
(`LatticeMap.TwistCompatibility`) evaluated on generators.

`exists_common_candidate₂`: two classes with stable images have a common
candidate realizing both images. This is `exists_common_candidate` for the index
type `Bool`.

`eq_of_candidate`: two generators in the domain of a candidate with the same
image are equal, since `Φ` is a linear equivalence and generators are injective.

## Injectivity

`extensionBasis_injective`: assume candidate existence, stable images in every
rank and a geometric reciprocity candidate `e`. Let `b = z b₀` and
`b' = z' b₀'` be stable decompositions with stable images `π₀`, `π₀'`, and
suppose `z π₀ = z' π₀'`. Then `π₀' = w π₀` with `w = z'⁻¹ z`. Since both are
unitary, `norm_eq_one_of_unramifiedTwist_unitary` gives `‖w‖ = 1`. A common
candidate `Φ` for `b₀` and `b₀'` sends the `fieldUnramified K w`-twist of `b₀` to
the twist of `π₀`, which is `π₀'`, the image of `b₀'`. By `eq_of_candidate` the
twist of `b₀` by `w` is `b₀'`. Hence `b = z' (w b₀) = z' b₀' = b'`.

## Surjectivity

`extensionBasis_surjective`: assume `SupercuspidalUnitaryFiniteOrderTwistStatement`
(module `HenniartExtensionInputs`). Any `π` is `z π₀` with `π₀` unitary of
finite-order central character. `StableSurjectiveAt` gives a class `b₀` of the same
rank whose stable image is `π₀`. Then `(z, b₀, π₀)` is a stable decomposition of
`z b₀`, and `extensionBasis_eq` shows that `z b₀` is sent to `π`.

`extensionMap_rankwiseBijective` transfers both properties to each rank, using
`extensionBasis_rank` and `sigma_extensionMap`. This is the published
`SupercuspidalRankwiseBijective`.
