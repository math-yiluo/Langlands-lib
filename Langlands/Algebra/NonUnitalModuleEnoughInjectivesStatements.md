# Renard I.5.2: actual duals of projectives and enough injectives

Authors: Worker 6 (shared statement draft and source correspondence),
Worker 490 (source audit, complete interface checks and submission).

Import `Langlands.Algebra.NonUnitalModuleEnoughInjectivesStatements`.
The four proposition definitions are in namespace
`Langlands.Algebra.NonUnitalModuleEnoughInjectives`.

These proposition definitions translate the lemma and corollary in David
Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, I.5.2, printed p.27 / PDF p.33. The registered original is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original page was read, including its formulas. The registered supplement
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF p.2 (the entry for the older printed p.29 lemma), corrects the older
proof to the composition Hom_A(X, dual(-)); the 2026 text already uses
that argument. Worker 490 read both governing passages and rendered
pages, checked the registered fingerprints, and also read I.4.1–2 on
printed pp.22–24 / PDF pp.28–30.

The algebra is the specified nonunital ring A with its specified complex
module structure, `IsScalarTower ℂ A A` and `SMulCommClass ℂ A A`, and
`IsIdempotented A`. These are the published complex-algebra compatibility
conditions. Modules keep their original additive action. Their complex
structure is recovered from that action by the published nondegenerate
scalar construction. There is no separately supplied module action that
could disagree with the original one.

The left category is exactly the published full subcategory
`NondegenerateModuleCat A`. The right category is
`RightNondegenerateModuleCat A`, namely the original nondegenerate category
over the multiplicative opposite ring. The source's suppressed left/right
convention is made explicit in both orientations. Each exact-Hom statement
installs `NondegenerateModuleCat.abelian A hA` and the corresponding
opposite-ring abelian structure, retaining the original pointwise Hom groups.

`DualProjectivityStatement` says that a source-Hom projective left object
has a source-Hom injective actual right dual, and a source-Hom projective
right object has a source-Hom injective actual left dual. The dual objects
are precisely the published `NonUnitalModuleDual.dualObject` and
`NonUnitalModuleDual.rightDualObject`. The latter uses the explicit
multiplicative double-opposite transport; it does not identify A with its
opposite. Both use the actual nondegenerate part of the algebraic complex
dual with the original precomposition action.

Projectivity and injectivity here are the published
`Langlands.Renard.HomProjective` and `Langlands.Renard.HomInjective`:
sequence exactness of the actual integer-module-valued covariant and
contravariant Hom functors respectively. The integer-valued presentation
retains the same additive exactness underlying the source's Hom functors.
The projective-to-injective conclusion is an assertion, with projectivity
only as the lemma's stated premise. No exactness of duality or equivalence
of categories is assumed as input.

`EnoughInjectivesStatement` asserts Mathlib's `EnoughInjectives` for both
actual categories. This means that each object M has an
`InjectivePresentation`: a genuinely categorical injective object J and a
monomorphism M → J. `InjectiveEmbeddingStatement` also exposes an original
intertwiner f : M → J and requires source-Hom injectivity of J, categorical
`Mono f`, and injectivity of the entire original underlying additive map.
It asserts existence of an embedding, with no minimality or injective
envelope property.

The source proves the lemma using (I.4.2.1), printed p.24 / PDF p.30,
which identifies Hom(-, dual P) with Hom(P, dual(-)), then exactness of
actual duality from I.4.1, printed p.23 / PDF p.29, and projectivity of P.
For enough injectives it takes a projective surjection P → dual M,
dualizes it to an embedding bidual M → dual P,
and composes with the canonical injection M → bidual M. These are
explanations of the source route; this statement pair contains no proof
of the three assertions.

The ring universe `uA` and module parameter `uM` are independent.
The dual-projectivity lemma is stated at the arbitrary carrier universe
`uM`, since the published dual has that same carrier universe. The two
existence assertions use the carrier universe `max uA uM`, permitting
actual Ae modules and the projective presentation of the dual to live in
the same category. No resizing principle or enough-injectives assertion
for a smaller carrier universe is included. The full closed definitions
and both unequal universe orders are checked in the Lean file.

`InjectivityAssertions` conjoins exactly these three families. Enough
injectives and the embedding assertion have no projectivity, exactness,
admissibility, finite-dimensionality, or reflexivity hypotheses. There is
no unit law. The assertions are limited to the stated complex-algebra
setting; general coefficients and proofs are separate obligations. The
projective existence theorem, I.5.3 free modules, general I.6
limits/colimits, and the remainder of the whole-book program are outside
this focused statement unit.
