# Exactness and injective preservation for the actual induction functors

Worker 691 states, without proving, the unnumbered theorem and corollary in
David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, I.2.4, printed pp.18–19 / PDF pp.24–25.
The registered original is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The theorem begins at the bottom of PDF24 and its proof and corollary continue
on PDF25. The conventions and nondegeneracy definitions are Chapter I and
I.1.2, printed pp.5–7 / PDF11–13; the constructions are I.2.2–I.2.3,
printed pp.15–18 / PDF21–24. Exactness and injectivity are defined in
A.VIII.1–2, printed pp.266–267 / PDF272–273. These passages were read directly.

The three principal declarations in `Langlands.Algebra` are closed `Prop`-valued
definitions. Each binds all its ring, action, idempotentedness, commutation
and source nondegeneracy inputs internally. Their arbitrary-ring additive scope
is an internal generalization of Renard's complex-algebra setting. The actual
integer-tensor quotient and original additive Hom are reused. Complex-linear,
coefficient and unitization agreement remain separate obligations of the parent.

`NondegenerateFInductionExactnessTheorem` uses the specified left A-action on
the actual additive carrier B and exactly `NonUnitalModule.rightRegular B`.
Its commutation and `IsNondegenerateBimodule A B B` hypotheses refer to precisely
those actions. It asserts `SequenceExact F ∧ SequenceLeftExact I`, where
F is the published `NondegenerateTensorFunctor.F` with that right regular action,
and I is the published `RenardHomFunctors.I`. At N, F has the actual carrier
`Tensor B B N.obj`, its published residual left A-action, and the actual
fixed-first-factor tensor maps. At M, I has the B-nondegenerate part of
`NonUnitalModuleHom A B M.obj`, with source-precomposition action
`(b • h)(b') = h(b' * b)`. Its maps are restricted original postcomposition.
No right A-action on B is supplied.

`NondegeneratePInductionExactnessTheorem` separately binds a right A-action on
B and exactly `NonUnitalModule.regular B` on the left. Its own commutation and
`IsNondegenerateBimodule B A B` hypotheses use those actions. It asserts
`SequenceLeftExact pseudoF ∧ SequenceRightExact P`, using the actual published
`RenardHomFunctors.pseudoF` and `NondegenerateTensorFunctor.P`. At N, pseudoF
is the A-nondegenerate part of `NonUnitalModuleHom B B N.obj`, with action
`(a • h)(b) = h(op a • b)`, for the specified right A-action on B; its maps
are restricted postcomposition. At M, P has carrier `Tensor A B M.obj`,
the published residual left regular B-action and fixed-first-factor tensor maps.
No left A-action is supplied in this family. The families need not coexist,
and no ring homomorphism, coefficient structure or unit-action law is required.

For all four exactness assertions, the ring universes uA and uB and the source
carrier universe v are independent. Each functor has source carrier v and
actual target carrier `max uB v`, because B is its fixed tensor or Hom argument.
Each conjunction concerns two functors separately; it asserts no categorical
composite between differently sized categories and performs no universe resizing.

The categories are the actual full subcategories `NondegenerateModuleCat`.
Each predicate uses precisely the named data `NondegenerateModuleCat.abelian`
at the appropriate carrier universe. Their inherited preadditive structures
agree by the published `abelian_toPreadditive`, and the actual functors'
published additive instances apply. No caller-supplied abelian structure or
exactness certificate occurs in a target.

`SequenceLeftExact` tests every `ShortComplex S` with `S.Exact ∧ Mono S.f`
and preserves both `(S.map F).Exact` and `Mono (F.map S.f)`.
`SequenceRightExact` instead tests `S.Exact ∧ Epi S.g` and preserves both
exactness and the boundary epimorphism. `SequenceExact` is their conjunction.
These are exactly the published predicates in
`Langlands.CategoryTheory.RenardExactFunctor`, including sequences with only
the stated one-sided boundary condition.

`NondegenerateIInductionInjectivityTheorem` has the same A–B hypotheses, and sets
the common carrier universe to `w = max uB v`. The actual I is specialized at
source w; its target carrier `max uB (max uB v)` is definitionally w.
For every actual X in the A-category at w it asserts both
`HomInjective X → HomInjective (I.obj X)` and
`CategoryTheory.Injective X → CategoryTheory.Injective (I.obj X)`.
The source predicate is the published exactness of the actual contravariant
integer-module-valued Hom functor. The companion checks reuse
`Langlands.Renard.homInjectiveComparison` to compare the two preservation forms.
Injectivity of X is intrinsic to the corollary. Neither exactness of F, an
adjunction, injectivity of the output nor a preservation certificate is an input.
This statement makes no transfer from a smaller source category to an enlarged
target category at arbitrary v.

Renard's proof route first uses right exactness of tensor and left exactness
of Hom (I.2.2), then exactness of the nondegenerate-part functor (I.1.2).
Left exactness of F additionally uses the regular-tensor contraction
(I.2.3.3), `b ⊗ n ↦ b • n`. That contraction is an additive identification
with the input when it is nondegenerate. An A-action on that input must be
defined before claiming an A-linear identification. The injectivity corollary
uses the actual adjunction `F ⊣ I` and exactness of F, identifying the
contravariant integer-module Hom functor with `Hom_A(F(-), X)`. These are
provenance and later proof obligations, and provide no proof of these targets.
The common carrier setting agrees with the separate categorical adjunction
statement; any use of that result must await its actual proof.

The supplementary registered `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read at PDF1–2 and PDF18–19. PDF1 gives `F ⊣ I` and `P ⊣ pseudoF`,
already incorporated in the governing 2026 edition. PDF18 corrects the
covariant/contravariant Hom map order and PDF18–19 retain a distinct complex
coefficient/unitization warning. The author's book section was checked on
1 November 2026: it separately links the corrected 2026 French edition and the
2010 errata. No separate 2026 errata link appears in that section. This is a
bounded navigation check, not an exhaustive assertion about errata.

The companion checks cover complete unapplied types, exact unfolding,
independent and unequal universes, named structures, original object/map
formulas, the common-universe equality, regular integer actions and subsingleton
interfaces. Zero rings and trivial nondegenerate modules are permitted.
The main assertions are unproved. Their exact-target proofs are separate
successors after publication, as are generic tensor/Hom exactness, coefficient
bridges, scalar restriction and the remaining I.2.3 comparisons. This statement
unit does not complete I.2.4 or the whole book.
