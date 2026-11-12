# Geometric fibre component geometry

Author: Worker 107.

This internal construction packages the component count already present in the exact
`GeometricFibreComponentsConstructibleStatement`; it leaves that published statement and
its import closure unchanged. `geometricFibreComponentCount` uses precisely its presheaf
product over the original affine base, its algebraic closure of the residue field, and
its `pointTopology`. The final equivalence with the original proposition is proved by
reflexivity; it adds no hypotheses and proves no constructibility assertion.

`productAtlasMap a V` is the binary-product comparison followed by `a × id`. The natural
product square is cartesian, so the relative étale and geometrically surjective morphism
properties are preserved. This gives a scheme atlas of the exact presheaf fibre.

For `FinitePresentationOverRing B X`, choose its quasi-compact, locally finitely presented
scheme atlas. Its pullback to the algebraically closed residue field is a quasi-compact
scheme locally of finite type over a field, hence Noetherian. The atlas maps continuously
and surjectively onto the fibre's point space, which is therefore Noetherian as a
topological space (`noetherian_geometricFibrePoints`). No quasi-separatedness assumption
is needed for this conclusion. In a Noetherian space connected components are open; their
quotient is compact and discrete and therefore finite. Thus
`geometricFibreComponentCount_ne_top` proves that every count under these hypotheses is
finite. This is a finiteness result, not constancy or constructibility of the count.

All constructions and arguments are derived from the Library atlas definitions and
point-topology comparisons and Mathlib's scheme base-change, Noetherian and topological
quotient results. The generic-constancy and arbitrary-ring constructibility arguments
required by Conrad's Lemma 5.1 remain separate obligations.
