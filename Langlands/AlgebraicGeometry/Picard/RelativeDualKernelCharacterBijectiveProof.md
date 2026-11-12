# Proof of relative all-test Cartier kernel bijectivity

Authors: Worker 195 (proof and explanation, drafted for Task 195) and
Worker 3548 (recompilation against the current Library and submission).

The theorem `Langlands.AbelianScheme.relativeDualKernelCharacterBijective`
has type `Langlands.AbelianScheme.RelativeDualKernelCharacterBijectiveStatement`
with the full universe-polymorphic telescope and no additional assumptions.
It retains arbitrary base and test schemes, the actual isogeny, the original
dual/Poincare constructor data, and the exact normalized character map.

The proof assembles published lemmas in two steps.

`relativeTrivialPullbackPicardZero` handles a rigidified family `L` over an
arbitrary test scheme `T` of any base `S`, whose actual homomorphism
pullback is trivial. Unfolding `IsPicardZeroFamily` (through
`IsGeometricallyPicardZero`) asks for translation invariance of the
fibre bundle at every algebraically closed field-valued point `s` of `T`.
The isogeny hypothesis survives base change first to `T` and then to `s`
(`IsIsogeny.baseChange`, applied twice).
The existing `homPullback_familyLineBundle_trivial` changes product order
and supplies the actual ordinary trivialization over `T`.
`homPullback_fibreLineBundle_trivial` carries it to the exact geometric
fibre bundle. The published algebraically closed criterion
`algClosedFieldTrivialPullbackTranslationInvariant_of`, supplied with
the published all-base injectivity theorem
`trivialPullbackCharacterInjective`, therefore gives exactly the required
translation invariance. There is no reduction of the entire test scheme
to its points: only the defined Picard-zero membership condition is tested
on fibres. All-test bijectivity remains a separate descent input.

The entry theorem introduces the seven constructor propositions, the base,
the two abelian schemes with their dual-scheme witnesses, inverse Poincare
bundles and evaluation isomorphisms, the isogeny and the test scheme, in
the order of the statement. It then applies
`dualKernelPointCharacter_bijective_of_classification` to this membership
result and the published arbitrary-base theorem
`trivialHomPullbackClassCharacter_bijective`. The latter supplies actual
line-bundle descent and classification on every test scheme. The former
comparison uses the universal rigidified Picard-zero parameter and the
existing intrinsic character. Their composition proves bijectivity of the
specified normalized beta, rather than of an independently chosen map.

This is an internal assembly. The original character convention and
arbitrary-base descent context are Edixhoven, van der Geer and Moonen,
*Abelian Varieties*, preliminary draft built 2012-02-08, Proposition (7.4),
printed pp.99–100 / PDF pp.103–104; Theorem (7.5), printed p.100 / PDF p.104,
gives the field isogeny context. Source registration and the distinction
between that field theorem and this derived relative target are recorded
in the unchanged statement Markdown. No dual-existence or geometry theorem,
isogeny assertion for the dual map, rank formula, polarization perfectness,
or relative pairing theorem is added by this proof.

The development check of this exact file reports no errors or warnings and
only the axioms `propext`, `Classical.choice` and `Quot.sound`.
