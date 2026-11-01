# Finite tests for monomorphisms from line bundles

`IsMonoDetector M E` is an internal predicate for a module sheaf `M` on a
scheme `X` and a set `E` of its points. It says that every actual sheaf map
`M → O_X` whose underlying abelian-group stalk maps are isomorphisms at all
points of `E` is a monomorphism of module sheaves.

`IsLocallyFreeRankOne.exists_finite_mono_detector` proves that such a finite
set exists for every locally free rank-one module sheaf on every compact,
locally Noetherian scheme, in arbitrary universe `u`. The set depends on the
module and selected local trivializations, but is independent of the map being
tested. No quasi-affineness, reducedness, integrality, connectedness or
nonemptiness is assumed. This helper supplies the Noetherian regularity step
of the quasi-affine line-bundle ideal embedding construction; it does not
supply the global section or the embedding.

The affine auxiliary theorem
`Langlands.SchemeModule.exists_finite_unitEnd_mono_detector` first treats
endomorphisms of the structure module. The finite set is the image in `X` of
the associated primes of its coordinate ring `A = Γ(X, O_X)`, using `X.isoSpec`.
Mathlib's `associatedPrimes.finite A A` applies because `A` is Noetherian.
An endomorphism of the structure module is scalar multiplication by its
coefficient. A stalk isomorphism at each selected point puts the coefficient
outside each associated prime, using the published scalar stalk/basic-open
comparison. Mathlib's
`biUnion_associatedPrimes_eq_compl_nonZeroDivisors` then makes it a
non-zero-divisor. Localization preserves that property on each principal
basic open, so the map is injective on sections over a basis, and therefore
on every stalk and on the sheaf itself.

For the general theorem, each local rank-one trivialization is refined to
an affine open. `restrictTrivializationOfLE` constructs the refined actual
module-sheaf isomorphism using the restriction composition comparison.
Compactness selects a finite subcover. On each selected chart the affine
associated-prime theorem supplies a finite set; their images in `X` have
finite union. For a map satisfying the detector condition, the local
trivializations turn its restriction into an endomorphism of the structure
module. The restriction/stalk comparison transports the assumed stalk
isomorphisms to this endomorphism, so the affine theorem makes it a
monomorphism. Conjugation by the trivializations returns a monomorphism on
the original restriction. Each global stalk lies in one of the selected
charts and is injective by the restriction/stalk natural isomorphism.
`mono_of_stalk_injective` finally proves monicity by sectionwise
injectivity and cancellation against zero.

This predicate and its constructors are derived internal infrastructure.
The proof uses the published Library's restriction and scalar-stalk
comparisons and the named Mathlib associated-prime, localization, compactness
and sheaf-stalk theorems. It introduces no scheme-level associated-point
notion and makes no assertion identifying the chosen global finite set with
an intrinsic associated-point set. It uses none of the line-bundle extension
or valuative conclusions excluded by the host task.
