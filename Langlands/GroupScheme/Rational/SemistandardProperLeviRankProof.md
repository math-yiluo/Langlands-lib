# Strict relative rank decrease for proper semistandard Levis

`Langlands.GroupScheme.semistandardProperLeviRank` proves the Library's
`SemistandardProperLeviRankStatement` over a field in any universe. For an
intrinsic semistandard index `p` relative to a maximal split torus `i`, assume
`p.parabolic ≠ ⊤` as subgroup functors on all test schemes. For any closed
connected reductive model `j : M ⟶ G` representing `p.levi`, the rational span of
the relative roots at `semistandardLeviSplitTorus p hj` has strictly smaller
dimension than the corresponding span at `i` in `G`.

`semistandardSpectralDynamicCoverage` gives a cocharacter of the chosen torus
whose dynamic parabolic and centralizer are `p.parabolic` and `p.levi`.
The canonical torus lift `a` satisfies `a ≫ j = i`. The cocharacter composed
with `a` is central in `M` by `isCentral_comp_iff_le_dynamicCentralizer`, so
rational character restriction along the cocharacter kills the Levi root
span by `relativeRootSpan_le_centralRestrictionKer`. The factorization also
places the Levi roots among the ambient roots by
`relativeRoots_subset_of_factor`.

If the ambient span were contained in the Levi span, restriction would
annihilate every rationalized ambient root. Rationalization is injective on
the character lattice of the split multiplicative group, so every ambient
root has zero integral pairing with the cocharacter.
`rootAnnihilatorCentrality` then makes the cocharacter central in `G`, and
`Dynamic.parabolic_eq_top_of_centralizer` identifies `p.parabolic` with the
top subgroup functor. Properness rules this out. The strict inclusion of
spans therefore gives strict inequality of their rational dimensions by
`Submodule.finrank_lt_finrank_of_lt`, using finite dimensionality of the
ambient span from `IsSplitTorus.finite_relativeRootSpan`.

The structural comparison supplies the strict semisimple rank decrease used
in the induction paragraph preceding VIII.2, printed p. 321 (PDF p. 87) of
J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)* (2003). The registered source is
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
