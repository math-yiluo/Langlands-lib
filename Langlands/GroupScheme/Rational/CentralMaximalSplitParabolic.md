# No proper rational parabolics with a central maximal split torus

Author: Worker 82.

Over any field `F` in universe `u`, let `G` be connected reductive
and let `s : S → G` be an actual central maximal split torus.
This unit proves that every actual parabolic subgroup over `F` is
the whole group, with equality on every test scheme.

`IsMaximalSplitTorus.isCentral_of_central_maximalSplitTorus` uses the
proved rational conjugacy of maximal split tori. Conjugation fixes the
central map `s`, so the resulting isomorphism of source tori identifies
any other maximal split torus map with a precomposition of `s`.
Precomposition preserves centrality.

Every ground-field cocharacter factors through some actual maximal
split torus by the published extension theorem. That torus is central
by the preceding argument, so
`IsMaximalSplitTorus.isCentral_cocharacter` proves centrality of the
cocharacter on all test schemes.

The proved parabolic/cocharacter classification expresses each rational
parabolic as the dynamic parabolic of a ground-field cocharacter.
The centrality just proved makes the dynamic centralizer, and hence
the dynamic parabolic, the whole group functor. The existing
`isIso_parabolic_of_central_cocharacters` therefore proves that the
original parabolic inclusion is an isomorphism.
`parabolicIsoOfIsCentral` packages this as an actual group-scheme
isomorphism whose forward map is exactly the supplied inclusion.
`range_parabolic_eq_top_of_isCentral` records equality of its entire
all-test image with the top subgroup functor.

All structural inputs are proved Library theorems. No supplied
conjugating point, cocharacter presentation, isomorphism, parabolic
nonexistence assertion or compactness premise is used. The result
allows a nontrivial central maximal split torus and makes no
split-rank-zero assumption.

This is internal derived algebraic infrastructure for the interpretation
of anisotropy as `P = G` in Springer, *Reduction theory over global
fields* (1994), §2.1, printed pp.211–212 (PDF pp.5–6), and the
proper-rational-parabolic contradiction in §3.5, printed p.215
(PDF p.9). It supplies that contradiction after an actual parabolic
over the ground field has been constructed; it does not construct a
Galois descent or a root lower bound. The registered source is
`springer-1994-reduction-global-fields`, SHA-256
`774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`,
file `literature/Reduction theory over global fields (Springer, 1994).pdf`.
No errata note exists. No adelic compactness assertion is proved here.
