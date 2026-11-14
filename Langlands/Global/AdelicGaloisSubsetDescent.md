# Compact representatives descend along Galois scalar extension, for subsets

This internal helper module takes the published scalar-extension descent of
compact principal representatives and proves a version for subsets. The
published theorem
`hasCompactNormOneRationalCover_of_scalarExtension_representatives` in
`Langlands.Global.AdelicGaloisBoundedRootCompact` needs one compact upper set
that meets the principal coset of every scalar-extended source point. Here the
compact upper set only has to meet the cosets of the source points that we care
about. The conclusion then gives a compact source set for exactly those points.
This is the form used in the descent step of Springer, *Reduction theory over
global fields* (1994), §3.6. There, only the points in the first case of the
dichotomy have compact principal representatives over the splitting field.

All fields and group schemes live in one arbitrary universe `u`. The adelic
carriers, the all-character norm-one subgroups `normOneSubgroup`, the principal
maps `rationalNormOne`, the subgroups `rationalNormOneSubgroup` and the map
`scalarExtensionNormOneMap` are the existing Library objects.

## Compact representatives in a left coset space

`LeftCosetSpace.exists_isCompact_representatives_of_isCompact` is stated for
an arbitrary locally compact topological group `H` (in any universe) and an
arbitrary subgroup `Γ`, normal or not. Let `Z` be a compact subset of
`LeftCosetSpace Γ`, the quotient whose classes are the cosets `Γ x`. Then there
is a compact `K ⊆ H` such that every `x` whose class lies in `Z` has a left
translate `c * x`, with `c ∈ Γ`, lying in `K`.

Proof. Choose a compact neighbourhood `K x` of each point `x`. The images of
their interiors under the quotient map are open, because the quotient map is
open (`isOpenQuotientMap_mk`). They cover `Z`, so finitely many of them do. Take
`K` to be the union of those finitely many compact sets. If the class of `x` is
in `Z`, it is the class of some `z` in one of the chosen interiors. Then
`c = z * x⁻¹` lies in `Γ` and `c * x = z ∈ K`.

## Subset descent

Throughout, `F` and `L` are number fields, `L` is a Galois extension of `F`, and
`G` is an affine group scheme of locally finite type over `F`. The upper group
is `AffineWeil.unitBaseChange F L G`, the base change of `G` to `L`.

`AdelicGaloisUnit.exists_isCompact_rational_mul_mem_of_scalarExtension` (left
form). Let `K` be a compact set of upper norm-one points. Then there is a
compact set `Ω` of source norm-one points with the following property. Take a
source norm-one point `g`, and suppose some upper rational point `q` has
`rationalNormOne q * scalarExtensionNormOneMap g ∈ K`. Then some source
rational point `r` has `rationalNormOne r * g ∈ Ω`.

Proof. Let `Z` be the preimage, under the published `scalarExtensionQuotientMap`,
of the image of `K` in the upper rational quotient. That image is compact
because the quotient map is continuous. The published theorem
`isClosedEmbedding_scalarExtensionQuotientMap` says the scalar-extension map of
rational quotients is a closed embedding, and preimages of compact sets under
closed embeddings are compact. So `Z` is compact. The previous lemma, applied to
the source norm-one group and the subgroup `rationalNormOneSubgroup F G`, gives
the compact set `Ω`. Under the hypothesis, the class of `g` lies in `Z`. This
holds because `scalarExtensionQuotientMap_mk_normOne` identifies its image with
the upper class of `scalarExtensionNormOneMap g`. Left multiplication by the
upper rational point `rationalNormOne q` does not change that class
(`LeftCosetSpace.mk_subgroup_mul`).

`AdelicGaloisUnit.exists_isCompact_mul_rational_mem_of_scalarExtension` (right
form). This is the same statement with principal factors on the right:
`scalarExtensionNormOneMap g * rationalNormOne q ∈ K` gives a source rational
point `r` with `g * rationalNormOne r ∈ Ω`. The right form is the convention of
`HasUniformNormOneRationalOrbitHeightBound`.

Proof. Apply the left form to the compact set `K⁻¹` and the point `g⁻¹`, using
`q⁻¹`. The resulting compact set is `Ω'`, and the final set is `Ω = Ω'⁻¹`.
Inversion is a homeomorphism and the maps involved are homomorphisms, so the
hypotheses and conclusions move across by inverting both sides.

## Provenance

This module is internal and does not formalize a numbered statement of the
literature. Springer (1994) §3.6 uses the closed embedding of rational quotients
`C(G,k) → C(G,l)` (his Lemma 1.3) to pass compactness from the splitting field
`l` down to `k`. The Library already proves that closed embedding, and this
module only adds the general-topology step that turns a compact subset of a
quotient into compact representatives. No new definitions are introduced.
