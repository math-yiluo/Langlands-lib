# The original common split torus of a represented geometric-lemma datum

Author: Worker 1776.

This internal adapter uses the split torus already present in the published
intersection datum. It chooses no new torus or representative. The original map
t into M′ is maximal split in G. Composing it with the inverse of the supplied
algebraic isomorphism φ gives `targetCommonTorusHom` into L′. The datum's
original compatibility equation proves that its ambient image is the source
torus conjugated by z⁻¹. Ambient isomorphism transport preserves maximal split
structure. Closedness of the four original inclusion maps also makes t maximal
split in M′; transporting by φ makes the new map maximal split in L′.

The general factorization lemma proves that a cocharacter centralized by an
ambient maximal split torus factors through that same torus. Its proof uses
all-test-scheme centralizer membership to obtain pointwise commutation, then
applies the existing maximal-split-torus factorization for a commuting split
torus map. It imposes no nonzero or injectivity condition on the cocharacter.

The field, canonical topology and represented parabolic data are those of the
published datum. The algebraic comparisons preserve the original maps. This
module does not prove parabolic dynamic realization, a Haar balance or the
closed orbit-comparison statement. It is a derivation from published point,
closed-subgroup and split-torus transport APIs, without an external source claim.

`targetCommonTorusHom` abbreviates the existing `D.leviTorus` from `Exponents.GeometricLemmaSplitComponent`. Its ambient composite and maximal splitness laws reuse `leviTorus_comp` and `isMaximalSplitTorus_leviTorus_comp`, respectively.
