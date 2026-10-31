# The integral closure over a complete DVF is not a field

The module proves NYLL M245.010 as the exact published closed proposition
`IntegralClosureNotIsFieldOfFiniteSeparableStatement.{u, v, w}`.
The public theorem is
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosure_not_isField_of_finite_separable`.
Its complete unapplied type is that target constant, with independent universe
parameters `u, v, w` in that order and no additional declaration arguments.

The entry module is
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.NotFieldProof`.
The published target in `FiniteIntegralClosure.DVRStatements` and all
published dependencies are used unchanged.

## Data, universes and scalar maps

The target quantifies, in order, over
`(K : Type u) (L : Type w) [Field K] [Field L] [Algebra K L]
(base : CompleteDVF.{u, v} K) [Algebra.IsSeparable K L]`
and concludes
`¬ IsField (integralClosure base.valuation.valuationSubring L)`.
The proof introduces exactly these parameters and the hypothesis that the
integral closure is a field. There is no `FiniteDimensional K L` premise, so
the theorem also covers infinite separable extensions and the trivial
extension `L = K`. The separability hypothesis is not used by the proof, as in
the source. The value group stored in `base` lies in `Type v`; its valuation is
complete and rank-one discrete as specified by `CompleteDVF`. None of the three
universes is identified with another.

Write `A := base.valuation.valuationSubring`, the actual valuation subring of
`K`, and `B := integralClosure A L`, the actual Mathlib subalgebra of elements
of `L` integral over `A`. The rings `A` and `B` lie in `Type u` and `Type w`,
respectively. The algebra map `A → L` is the inclusion `A → K` followed by
`algebraMap K L`; `algebraMap A B` corestricts it to the integral closure
(`Subalgebra.algebra`), so the underlying element of `algebraMap A B x` in `L`
is, by definition, `algebraMap K L x`. `B` carries its subalgebra ring
structure `Subalgebra.toCommRing`.

## Implemented proof

1. Injectivity of `algebraMap A B`. If `algebraMap A B x = algebraMap A B y`,
   applying the coercion `B → L` gives `algebraMap K L x = algebraMap K L y`
   (definitional equality of the scalar maps above). The ring map
   `algebraMap K L` is injective because `K` is a field and `L` is nontrivial:
   Mathlib's `RingHom.injective` for simple rings
   (`Mathlib/RingTheory/SimpleRing/Basic.lean`, line 67), with the instance
   `DivisionRing.isSimpleRing` (line 52). Hence `(x : K) = (y : K)`, and
   `Subtype.ext` gives `x = y`. This is a local `have`, not a declaration.
2. Descent of the field property. Mathlib's instance
   `integralClosure.AlgebraIsIntegral`
   (`Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean`,
   line 195) gives `Algebra.IsIntegral A B`. The lemma
   `isField_of_isIntegral_of_isField` (same file, line 625), applied to the
   injectivity from step 1 and the assumed `IsField B`, gives `IsField A`.
3. Contradiction. `IsDiscreteValuationRing.not_isField A`
   (`Mathlib/RingTheory/DiscreteValuationRing/Basic.lean`, line 70) says that
   `A` is not a field. The instances it needs are found by instance search:
   `IsDomain A` is `ValuationSubring.instIsDomainSubtypeMem`, and
   `IsDiscreteValuationRing A` is Mathlib's
   `Valuation.valuationSubring_isDiscreteValuationRing`
   (`Mathlib/RingTheory/Valuation/Discrete/Basic.lean`, line 449). The latter
   needs the value group of `base.valuation` to be cyclic (Mathlib's instance
   from `IsRankOneDiscrete`, same file, line 133) and nontrivial (Mathlib's
   instance from `Valuation.IsNontrivial`,
   `Mathlib/RingTheory/Valuation/Basic.lean`, line 622, which in turn comes
   from `IsRankOneDiscrete`, `Discrete/Basic.lean`, line 137). The
   `IsRankOneDiscrete` instance of `base.valuation` is the published
   projection `Valuation.IsCompleteDiscrete.isRankOneDiscrete` of the stored
   field `base.instCompleteDiscrete`; both are instances declared in the
   published `Complete.Definitions` module.

A private check in the approved environment confirmed these instance
resolutions with `#synth`, the definitional equation in step 1 by `rfl`, and
that the trivial extension `L = K` is an instance of the theorem. Inspection
of the theorem reports kind `theorem`, universe parameters `u, v, w`, and only
the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Source correspondence and adaptations

The source is Naganori Yamaguchi's ClassFieldTheory at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteIntegralClosure.lean`:
universe line 23, ambient variables 30–31, M245.010 comment 307–308, the
`omit [FiniteDimensional K L] in` clause at 309, docstring 310, signature
311–314 and proof 315–327. The original name
`ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosure_not_isField_of_finite_separable`
becomes the public theorem above with the `Langlands.NYLL` prefix and the exact
closed target. The source docstring speaks of a "nontrivial finite separable
extension", but its signature assumes neither finiteness (because of the
`omit` clause) nor nontriviality; the published target and this proof follow
the signature.

The proof keeps the source route: integrality of `B` over `A`, injectivity of
`algebraMap A B`, `isField_of_isIntegral_of_isField` and
`IsDiscreteValuationRing.not_isField` for `A`. The explicit modifications are:

- The closed-target signature, the explicit independent universes `u, v, w`,
  and the source abbreviation `base.valuationSubring` expanded to the actual
  valuation subring `base.valuation.valuationSubring`.
- The source obtains injectivity through the standalone wrappers
  `CanonicalIntegralClosure.algebraMap_injective` (M245.001, lines 33–47) and
  `CanonicalIntegralClosure.faithfulSMul` (M245.002, lines 49–59), installs a
  local `FaithfulSMul A B` instance and recovers injectivity from it with
  `FaithfulSMul.algebraMap_injective`. Here the injectivity argument of
  M245.001 is done inline as a local `have` and passed directly to
  `isField_of_isIntegral_of_isField`; neither wrapper nor the faithful action
  is ported or exported.
- Injectivity of `algebraMap K L` comes from `RingHom.injective` (a field map
  into a nontrivial ring) instead of the source's
  `FaithfulSMul.algebraMap_injective K L`.
- The source installs `Algebra.IsIntegral A B` with an explicit `change` and
  `infer_instance`; here instance search finds
  `integralClosure.AlgebraIsIntegral` directly.
- The NYLL upstream imports are replaced by the published target and focused
  Mathlib imports.

Worker 106 supplied routing and source/API observations only, no
implementation draft, and no other worker's adapted Lean content was reused.

## Imports and scope

The direct imports are the published `FiniteIntegralClosure.DVRStatements`
(the target, which imports the published `Complete.Definitions`), plus Mathlib's
`RingTheory.DiscreteValuationRing.Basic` (`IsDiscreteValuationRing.not_isField`),
`RingTheory.IntegralClosure.IsIntegralClosure.Basic`
(`integralClosure.AlgebraIsIntegral` and `isField_of_isIntegral_of_isField`),
`RingTheory.SimpleRing.Basic` (`RingHom.injective` and
`DivisionRing.isSimpleRing`) and `RingTheory.Valuation.Discrete.Basic` (the
discrete valuation ring instance of the valuation subring).

The only public addition is M245.010's proof. There is no added hypothesis,
helper declaration, global instance, axiom, chosen extension valuation,
finiteness, localness, faithfulness or discrete valuation ring assumption on
`B`. The adic completeness of `base` is not used; only its rank-one
discreteness is. The
sibling M245.011 statement in the same target module, that `B` is a discrete
valuation ring for finite separable extensions, is not proved here.

## Attribution and source records

The registered source `external-lean-reuse-snapshots-2026-10-21` has fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The source root is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The verified SHA256 of `FiniteIntegralClosure.lean` is
`43c21425b2c39e7e6e5d2bca1f2b615c5c29e9d91e69d32d079e593df3170094`.

The attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
It has no entry specific to `FiniteIntegralClosure.lean`. No applicable
erratum was found.

The original copyright and author header is retained verbatim: copyright 2026
Naganori Yamaguchi; authors Naganori Yamaguchi (assisted by OpenAI Codex), under
Apache-2.0. The existing unmodified
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) accompany this adaptation.
Worker 764 made the modifications listed above on 30 October 2026 and wrote
this Markdown. The approved environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
