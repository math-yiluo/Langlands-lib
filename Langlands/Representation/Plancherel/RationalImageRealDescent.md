# Real homomorphisms descended to the actual valuation image

Author: Worker 20.

This is a derived algebraic construction over the published actual rational
character valuation image. It implements the factorization step used after
norm-kernel annihilation in the proof route for
`Langlands.Plancherel.RationalSmoothRealDescentStatement`. It does not prove that
smooth real homomorphisms annihilate that kernel.

For any nonarchimedean local field `F` in universe `u`, any actual group scheme
`M` over `Spec F`, and any homomorphism
`f : GroupScheme.rationalPoints M →* Multiplicative ℝ`, the definition
`rationalImageRealDescend M f hker` constructs an additive real functional on
`Additive (rationalDiscreteValuationImage M)`. Its explicit premise is
`hker : rationalCommonNormKernel M ≤ f.ker`. There is no connectedness,
reductivity, splitness, smoothness, or rational-point topology premise here.

The construction uses `MonoidHom.liftOfSurjective` along the existing
`rationalValuationImageProjection M`. The published
`rationalValuationImageProjection_ker` identifies its kernel with the common
norm kernel, and `rationalValuationImageProjection_surjective` supplies the
surjection. Both are in
`Langlands.Representation.Plancherel.RationalImageCharacters`. Finally
`MonoidHom.toAdditive` expresses the descended real homomorphism additively.

`rationalImageRealDescend_projection` gives the exact evaluation formula

`rationalImageRealDescend M f hker (Additive.ofMul (rationalValuationImageProjection M g)) = (f g).toAdd`.

`rationalImageRealDescend_unique` proves that any functional satisfying these
evaluations equals the constructed one: choose a rational-point preimage of
each image element and compare the two evaluations.
`existsUnique_rationalImageRealFunctional` packages existence and uniqueness.
No residue-cardinality scalar, logarithm, or sign change occurs.

The provenance is the elementary universal property of the already published
surjective valuation projection. The broader source correspondence with Renard
V.3.19, printed p.115 / PDF p.121 of the 9 July 2026 French edition, is recorded
in the imported target's companion Markdown. This module supplies only the
algebraic factorization after its displayed kernel premise has been proved.
