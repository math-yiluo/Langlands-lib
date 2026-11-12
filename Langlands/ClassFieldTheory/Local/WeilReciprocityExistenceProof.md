# Existence of actual geometric local Weil reciprocity

Authors: Worker 95 and Worker 201.

This module proves the exact published
`Langlands.LocalClassField.WeilReciprocityExistenceUniqueness` target.
The final theorem is
`Langlands.LocalClassField.geometricWeilReciprocityExistenceUniqueness`.
It retains every prime, arbitrary carrier universe, field and supplied
topological datum, with no additional hypothesis. The imported profinite
existence and actual Weil uniqueness proofs are reused.

This proof is an internal derivation from the imported Library theorems.
It uses the existing actual residue-degree map and the topology of the
integer-Frobenius pullback, without constructing another Weil group.

The degree comparison uses actual finite unramified extensions of every
positive degree. The first two lemmas transport equality of the absolute
residue actions to congruences for supplied valuation rings and then to equality
of restriction to an unramified finite extension. This explicitly compares the
norm used by the absolute residue construction with the spectral norm used by
the finite unramified coordinate. Residue naturality identifies the inverse
arithmetic cyclic coordinate with geometric degree on the Weil projection;
density of that projection extends the comparison to the absolute Galois group.
The full profinite geometric congruence fixes the coordinates of reciprocity on
elements of order one. Multiplying any nonzero element by a suitable power of
a uniformizer gives order one, so cancellation determines all its coordinates.

All positive modular quotients separate the actual profinite completion of
the integers: for a finite-index subgroup of the integers, its index multiple
lies in the subgroup. This supplies commutativity of that completion and the
continuous Galois-abelianization degree map. Comparing every modular reduction
proves that reciprocity sends an element to Frobenius raised to its order.

Every degree-zero Galois class lies in the reciprocity image of the valuation
units. To prove this, fix an open subgroup of the compact abelian Galois group
and let its index be \(N\). Reciprocity density provides an approximating
element whose order is divisible by \(N\). Dividing this element by the
corresponding power of a uniformizer makes it a valuation unit without changing
its image modulo the chosen subgroup. Compactness of the valuation units then
turns this approximation into an exact preimage.

The two range lemmas have no injectivity premise. The forward lemma chooses
an absolute Galois representative of a reciprocity image; the degree identity
puts this representative and the element's order in the actual Weil pullback,
and projection gives the required abelianized class. Conversely, divide a Weil
class's Galois image by the reciprocity image of a uniformizer to its integer
degree. The result has degree zero, so the preceding compactness argument gives
a valuation-unit preimage. Multiplication by the same uniformizer power
recovers the original image and degree.

The companion [topological assembly](WeilReciprocityExistenceAssembly.md)
pairs the Weil-to-Galois map with Weil degree and pairs reciprocity with
normalized order. These are inducing injective maps to the product of the
Galois abelianization with the discrete integers, because their degree kernels
are compact. The two range lemmas identify the ranges and give a continuous
group equivalence in both directions. The coordinate identities provide
geometric order and identify its induced Galois map with the full normalized
profinite reciprocity map. Hence density, all finite norm kernels, finite
surjectivity, restriction compatibility and geometric residue normalization
are inherited without weakening that relation. The published uniqueness proof
then gives the exact existential-unique target.

All inverse values lie in the actual topological Weil abelianization.
The use of a representative in the forward range proof establishes only an
existence statement; no nonabelian Frobenius lift is selected as part of the
candidate. All target files and their imported published pairs are unchanged.
