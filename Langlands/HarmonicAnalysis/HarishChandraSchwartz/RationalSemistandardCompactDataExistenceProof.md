# Compact-picture data for actual semistandard parabolics

`Langlands.HarishChandraSchwartz.RationalSemistandard.compactDataExistence`
proves `CompactDataExistenceStatement`. For each intrinsic index
the proof supplies a compact open subgroup in the canonical rational-point
topology, continuity of the literal Levi projection and a factorization in the
order \(G(F)=P(F)K\). Waldspurger (2003), §I.1, printed pp. 238–240, uses this
product in the compact picture. The paper is registered as
`waldspurger-2003-plancherel`.

The explicit local-field premise supplies the local instance. Smoothness of
the connected reductive group supplies local finite type.
`Langlands.HarishChandraSchwartz.rationalIwasawaCompactExistence` gives `K` and
the point product for an empty-index standard parabolic. Its proof
(`RationalIwasawaCompactExistenceProof`) uses depth-zero root groups at an apartment point and the relative
Tits system. `standardParabolic_empty_eq_dynamic_of_generic` and
`genericMinimalParabolic` give minimality for the empty-index parabolic.

For an intrinsic index `p`, `parabolicContainsMinimalStatement` puts a minimal
parabolic `Q` inside `p.parabolic`. `minimalParabolicConjugacy` gives a rational
conjugator from the first minimal parabolic to `Q`. Evaluation on the identity
test scheme and `SubgroupFunctor.mem_rationalPoints_comap_innerIso_hom` make
this an assertion about literal rational-point subgroups. The two lemmas
`IsIwasawaPair.exists_mem_conjugator` and `IsIwasawaPair.of_mem_conjugator`
choose a conjugator in `K` and retain the same `K` in the product with `Q`.
`IsIwasawaPair.mono` enlarges the parabolic factor to `p.parabolic` on points.
`RationalSemistandard.projectionContinuity` and `factorization_subtype`
give the final fields of `CompactData p`.
