# Joint restriction of actual unramified characters

Authors: Worker 159 (algebraic implementation), Worker 5102 (wall integration interface).

This is an internal algebraic reduction for wall unramified-twist surjectivity. It
uses the published actual rational-character valuation image and the published
extension theorem for complex characters. It makes no assertion that the wall
geometry itself supplies its finite-index or injectivity hypotheses.

Let `F : Type u` be a nonarchimedean local field and let `f : H ⟶ G` and
`g : H ⟶ K` be morphisms of group schemes over `Spec F`.

The theorem `rationalValuationImageMap_prod_injective_of_nsmul` assumes that for
every actual rational character `ξ` of `H` there are a natural number `n > 0` and
actual rational characters `ψ` of `G` and `η` of `K` satisfying
`n • ξ = characterRestrict f ψ + characterRestrict g η`. It proves injectivity of
the product of the two actual valuation-image maps. Two valuation functionals
with the same images agree on both character restriction ranges. Their difference
therefore vanishes on the sum. The displayed spanning hypothesis places a positive
multiple of each character in that sum; cancellation of multiplication by this
positive integer in `ℤ` proves equality of the original functionals. No
affineness, reductivity, or rational Levi hypotheses are needed for this implication.

The corollary `rationalValuationImageMap_prod_injective_of_finiteIndex` assumes that
the sum of the two additive subgroups
`(GroupScheme.characterRestrict f).range` and
`(GroupScheme.characterRestrict g).range` has finite index in the actual rational
character group of `H`. Finite index puts a positive multiple of every character
in that sum. Decomposing this element as a sum of elements of the two ranges gives
the preceding spanning hypothesis and hence the same injectivity conclusion.

For affine `G`, `H`, and `K`, equip their actual rational points with the canonical
`rationalPointTopology`. The definition
`rationalUnramifiedCharacterProductRestrict f g` is the group homomorphism
`X(G) × X(K) → X(H)` sending `(ψ, χ)` to `ψ|_H * χ|_H`, where `X` is the published
continuous unramified-character group defined by the common rational norm kernel.
The associated application lemma states this formula exactly. The definition
asserts only a group homomorphism, without an additional continuity claim about
the map between character spaces.

If in addition `G` and `K` are locally of finite type and the joint valuation-image
map is injective, then
`rationalUnramifiedCharacterProductRestrict_surjective_of_injective` proves this
homomorphism surjective. The proof descends a given character of `H(F)` to the
actual discrete valuation image of `H`. The published theorem
`Langlands.Topology.exists_complex_character_extension` extends it along the
injective joint map to the product of the valuation images of `G` and `K`.
Restriction to the two factor inclusions gives two characters. Every character
of these discrete images is continuous; the published canonical pullback
constructs continuous unramified characters of the two rational-point groups.
Multiplicativity on the product and the extension identity give the required
factorization on every rational point of `H`.

The theorems
`rationalUnramifiedCharacterProductRestrict_surjective_of_nsmul` and
`rationalUnramifiedCharacterProductRestrict_surjective_of_finiteIndex` compose
these implications. Thus the geometric wall proof may supply joint injectivity
directly, the positive-integer spanning hypothesis, or finite index of the sum of
actual character restriction ranges. All results retain the arbitrary field universe `u`. This module proves
only these conditional algebraic implications and is not a proof of
`WallUnramifiedTwistSurjectivityStatement`.
