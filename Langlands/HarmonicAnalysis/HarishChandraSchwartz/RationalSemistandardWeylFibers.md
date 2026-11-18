# Parabolic fibers over Weyl-conjugate Levis

The inner sum in Waldspurger's VI.3 averaging formula ranges over the
parabolics `P(s.M)`. In VII.2.4 the association count uses the equality
of the cardinalities of `P(M)` and `P(s.M)`. See *La formule de
Plancherel pour les groupes p-adiques (d'après Harish-Chandra)*, I.1,
printed p. 238 (PDF p. 4), VI.3, printed p. 306 (PDF p. 72), and Remark
VII.2.4, printed p. 320 (PDF p. 86). Source `waldspurger-2003-plancherel`.

The construction takes connected reductivity, maximal splitness, and
the exact `SemistandardSpectralDynamicCoverageStatement` as inputs.
`normalizerConjugateIndex` uses `CocharacterPresentation.ofCoverage`
to present the original intrinsic triple. A normalizer point
conjugates its cocharacter by the actual automorphism of the fixed
torus. The formulas for the new parabolic, Levi and radical identify
all three with the inverse-isomorphism preimages of the original
functors. These formulas come from functoriality of the dynamic
subgroups and identify the triple independently of the cocharacter
presentation. Conjugation by the inverse point recovers the original
triple. The published `relativeWeylCocharacterAction` proves independence
of the lift on the whole triple.

With the explicit source Levi containment `torusCentralizer i ≤ M.val`,
`weylConjugateLevi` is the existing all-test
`relativeWeylConjugateSubgroupFunctor` at `M` and `s`, realized in
`SemistandardSpectralLevi`. The resulting `weylParabolicFiberEquiv`
conjugates each actual parabolic triple over `M` into the fiber over
`s.M`, and uses inverse conjugation in the other direction.
`weylParabolicFiberEquiv_mk` computes the equivalence using any
normalizer lift. `card_weylConjugateParabolicFiber` follows by taking
the cardinality of the equivalence. This is the geometric parabolic
fiber comparison for the average and the association count.
