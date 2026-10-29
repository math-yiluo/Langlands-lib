# Surjective canonical localization map: proof for the actual quotient

Author: Worker 702, for task `aaa638ed-702c-47b2-8d19-c05cdf9adb43`
under the whole-book Renard parent `f5d1f399-a1f8-4ab5-a981-90b92abd4857`.

This module imports the unchanged published statement module
`Langlands.Algebra.RenardSurjectiveLocalizationStatements` and the
published proved kernel results in
`Langlands.Algebra.RenardEndomorphismLocalizationKernelProof`. Its closed
theorem `Langlands.Renard.EndomorphismLocalization.surjectiveIotaQuotientStatements`
has exactly the type
`Langlands.Renard.EndomorphismLocalization.SurjectiveIotaQuotientStatements.{u,v}`.
It proves both the commutative-ring statement and the explicit field
specialization, with independent coefficient and module universes.

## Source and provenance

The field corollary is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, Appendix A.III.1, the
unnumbered corollary following example 5 and its lemma,
printed p. 253 / PDF p. 259. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 702 read PDF pp. 258–259 and visually inspected PDF p. 259.
The source assumes that the canonical map from the vector space to its
endomorphism localization is surjective and concludes that the localized
pair is isomorphic to the quotient by the union of the kernels of the
endomorphism's powers, with its induced endomorphism.

The extension to arbitrary commutative rings and the uniqueness of an
equivalence compatible with the canonical maps are internal strengthenings,
already specified in the published statement Markdown. The proof uses
the proved kernel equality and the first isomorphism theorem for the
actual quotient. It does not follow the book's proof through localization
of the quotient.

Worker 702 also checked the registered supplementary author errata
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pp. 18–19. Those pages list corrections to the older edition and
contain no correction to this corollary. This is a limited older-edition
check; the 2026 source governs. The public Appendix A discrepancy note
concerns the scalar-inverse wording in example 4 and does not alter this
corollary's use of the actual endomorphism localization.

## Implemented proof

The helper `existsUnique_quotientEquiv_of_surjective` works for every
commutative ring `R : Type u`, every module `V : Type v`, and every
`a : Module.End R V`. Its only additional hypothesis is
`Function.Surjective (iota a)`.

First, `powerKernel_def` and the published proved theorem
`ker_iota_eq_iSup` identify the actual submodule `powerKernel a` with
`LinearMap.ker (iota a)`. Thus `Submodule.liftQ` descends `iota a` to a
linear map `f : PowerKernelQuotient a →ₗ[R] Localized a`. On a class
represented by `z`, this map is definitionally `iota a z`.
`Submodule.ker_liftQ_eq_bot'` and `LinearMap.ker_eq_bot` prove that `f`
is injective. The assumed surjectivity of `iota a` proves that `f` is
surjective, by taking the class of any preimage.

`LinearEquiv.ofBijective` turns `f` into a linear equivalence `d`, and
the desired equivalence is its inverse `e`. The inverse identity
`d.symm_apply_apply` gives
`e (iota a z) = quotientProjection a z` for every `z`. Extensionality
then gives the canonical-map equation.

For the operator equation, surjectivity of `iota a` allows an arbitrary
localized element to be written as `iota a z`. Rewriting with the published
`iota_intertwines`, the preceding canonical-map identity, and
`quotientEnd_projection` gives equality of the two composites. For
uniqueness, any other compatible equivalence has the same value on each
`iota a z` by its canonical-map equation. Surjectivity again covers the
whole localization, and `LinearEquiv.ext` proves equality.

The closed aggregate theorem applies this helper first to all
commutative rings, then to fields through their commutative-ring
instances. It has no section parameters or added hypotheses.
All constructions are the actual published `Localized`, `iota`,
`localizedEnd`, `powerKernel`, `PowerKernelQuotient`,
`quotientProjection`, and `quotientEnd`. Zero rings and zero modules are
allowed, with no finiteness, Noetherianity, stabilization or invertibility
assumption on the original endomorphism.

## Scope

This proves the complete published surjective-canonical-map aggregate.
The comparison with localization of the quotient, the inverse-power
extension converse, general possibly nonunital algebra actions,
categorical packaging, localization exactness and the final C.II
finite-localization proposition remain separate parent obligations.

## Development checks

Using environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, approved
service check `0cd11780-df2d-4dfd-90ec-6945c7c70998` compiled the proof
and inspected the aggregate with zero errors or warnings. Its universe
parameters are `u` and `v`, and its only axioms are `propext`,
`Classical.choice` and `Quot.sound`. Private diagnostic
`3ee6aa98-14d5-4cf3-828b-b8f02e4375c0` printed both complete theorem
types and checked direct assignment of the unapplied aggregate theorem
to the published target. These development checks do not supply
independent acceptance or publication.
