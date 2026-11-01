# Closed support bounds for scheme modules

`HasSupportDimensionLT M e` means that there is a closed subset `Z` such that `M` vanishes
on the open complement of `Z`, and every irreducible closed subset of `Z` has height less
than the natural number `e` in the poset of irreducible closed subsets of the scheme.
For a nonzero module, the customary support dimension bound `d` uses `e = d + 1`.
The definition does not require that `Z` be the smallest support or that the module be
quasi-coherent or finitely generated.

The companion lemmas preserve this bound under isomorphisms, increasing `e`, taking a
kernel from a bounded source, and taking a cokernel into a bounded target. A zero module
has every bound, and bound zero forces the module to vanish. A global bound `d` on the
topological Krull dimension supplies bound `d + 1` for every module.

On a noetherian separated scheme, an affine locally quasi-coherent module with bound `e`
has zero actual relative cohomology over any affine base in every degree at least `e`.
This is a direct application of the published closed-support vanishing induction.

Vanishing on an open excludes that open from the actual abelian stalk support: the
restriction is zero, and the natural restriction-stalk isomorphism identifies its stalks
with those of the original module. In a T0 space an irreducible closed subset of height
zero is a singleton. Indeed it is minimal among irreducible closed subsets, so the
closure of any of its points is the entire subset; the T0 property then identifies any
two of its points. A noetherian closed subset whose irreducible closed subsets have
height less than one is consequently a finite union of closed singletons. Applying the
stalk exclusion lemma shows that bound one gives finite closed stalk support, without
an additional coherence hypothesis.

This is internal infrastructure for support induction in the actual Euler-polynomial
task, not a proof of polynomiality or ample positivity. Its definition repackages the
hypotheses of `NoetherianVanishing.isZero_relativeCohomology_of_height`; the closure,
minimal-height, finite irreducible decomposition, and restriction-stalk arguments are
derived from the imported Library and Mathlib results. The dimension shift and use in
Euler induction follow the support-dimension induction in Stacks Project, Lemma 33.45.1
(tag 0BEM), in the registered numerical-intersections source. This module supplies no
generic trivialization or lower-support coherent devissage assertion.
