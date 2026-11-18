# Transporting finite Cartan coverings to the intrinsic standard Levi

This internal module transports the existing literal standard-Levi Cartan
covering to the canonical representing Levi scheme, at the exact inherited
compact subgroup. It composes published subgroup, root and point comparisons
and introduces no original-literature assertion. It does not construct a
Cartan covering or a simultaneous standard basis from scratch.

For any selected root set `J`, `mem_centralizerPoints_leviScheme` identifies
the intrinsic torus-centralizer points with the exact preimage of the ambient
torus-centralizer points under `rationalPoints.map (Standard.leviHom i nu J)`.
Its proof applies the published torus-centralizer comap theorem for a
monomorphic homomorphism and the exact factorization
`Standard.leviTorusHom_comp`. No connected reductivity, maximality or chamber
hypothesis is needed for this comparison.

`leviSchemeCentralizerPointLift` lifts each original ambient torus-centralizer
point through `leviSchemePointsEquiv`. Such a point belongs to the standard
Levi, by the published centralizer containment. The preceding comap comparison
proves that the lift belongs to the intrinsic torus centralizer. Its
`map_leviSchemeCentralizerPointLift` theorem states that the actual Levi
embedding sends the lift to the original point exactly.

Under connected reductivity, a maximal split torus, a generic cocharacter
and `J` contained in the ambient simple roots,
`simpleRelativeRoots_leviScheme` derives that the intrinsic Levi's simple
roots are exactly `J`, as subsets of the same character lattice. It specializes
the published `standardLeviStandardFamilies` theorem, using the published
standard-Levi connected-reductivity theorem and the canonical represented
closed Levi embedding.

`finiteCartanCovering_leviScheme` concludes
`FiniteCartanCovering F (Standard.leviTorusHom i nu J) nu
(leviSchemeCompact K0 i nu J)` from the original
`StandardLeviCartanCovering F i nu J K0`, under those same algebraic
hypotheses. It maps the finite ambient centralizer set through the proved
lift. For each intrinsic point, it applies the original literal-Levi cover
to its image, pulls both compact factors back through the canonical point
homeomorphism, and uses the simple-root equality to retain precisely the
same uniformizer chamber. The compact factors lie in the preimage
`leviSchemeCompact K0 i nu J`; applying the injective Levi point map proves
the resulting product equality. The torus factor agrees by
`Standard.leviTorusHom_comp`.

The result keeps the original `K0`, `J`, cocharacter and finite covering,
and does not replace them by unrelated existential data. It works over any
nonarchimedean local field and general connected reductive groups, with no
splitness, quasisplitness or characteristic restriction. Openness and
compactness of `K0` are not needed for this transport implication.

This module proves no inherited simultaneous-standard-basis property, no
Iwasawa decomposition, no analytic estimate and no wave-packet Schwartz
membership. Those are separate obligations in consumers of the transported
Cartan cover.
