# Localness of the finite integral closure

The module proves NYLL M245.006 as the exact published closed proposition
`IntegralClosureIsLocalRingOfFiniteSeparableStatement.{u, v, w}`.
The public theorem is
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosure_isLocalRing_of_finite_separable`.
Its complete unapplied type is that target constant, with independent universe
parameters `u, v, w` in that order and no additional declaration arguments.

The entry module is
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.LocalnessProof`.
The published target in `FiniteIntegralClosure.LocalnessStatements` and all
published dependencies are used unchanged.

## Data, universes and scalar maps

The target quantifies, in order, over
`(K : Type u) (L : Type w) [Field K] [Field L] [Algebra K L]
[FiniteDimensional K L] (base : CompleteDVF.{u, v} K) [Algebra.IsSeparable K L]`.
The proof introduces exactly these parameters. The value group stored in `base`
lies in `Type v`; its valuation is complete and rank-one discrete as specified
by `CompleteDVF`. None of the three universes is identified with another; the
universe parameters are passed unchanged as `.{u, v, w}` to the accepted fiber
theorem.

Write `A := base.valuation.valuationSubring`, the actual valuation subring of
`K`, `m := IsLocalRing.maximalIdeal A`, and `B := integralClosure A L`, the
actual Mathlib subalgebra of elements of `L` integral over `A`. The rings `A`
and `B` lie in `Type u` and `Type w`, respectively. `A` is local by Mathlib's
valuation-subring instance. The algebra map `A → L` is the inclusion `A → K`
followed by `algebraMap K L`; `algebraMap A B` corestricts it to the integral
closure (`Subalgebra.algebra`). The conclusion is `IsLocalRing B` for this
actual ring.

## Implemented proof

1. The accepted M245.005 theorem
   `integralClosure_base_maximal_fiber_subsingleton_of_finite_separable.{u, v, w} K L base`
   gives `Subsingleton (PrimeSpectrum (m.Fiber B))`, where `m.Fiber B` is
   Mathlib's actual fiber `m.ResidueField ⊗[A] B` over the canonical scalar
   maps above. It is installed as a local `have` instance.
2. Every maximal ideal lies over `m`. For `M : MaximalSpectrum B`, Mathlib's
   instance `integralClosure.AlgebraIsIntegral` gives
   `Algebra.IsIntegral A B`, so
   `Ideal.isMaximal_under_of_isIntegral_of_isMaximal` shows that the
   contraction `M.asIdeal.under A` is maximal. Since `A` is local,
   `IsLocalRing.eq_maximalIdeal` identifies it with `m`. Together with
   primality of `M.asIdeal`, this gives `M.asIdeal ∈ m.primesOver B` (the
   `LiesOver` field is `m = M.asIdeal.under A`).
3. Any two maximal ideals agree. Let
   `e := PrimeSpectrum.primesOverOrderIsoFiber A B m`, Mathlib's order
   isomorphism from primes of `B` over `m` to the prime spectrum of
   `m.Fiber B`. For maximal ideals `M` and `N`, their images under `e` agree
   because the fiber spectrum is a subsingleton; injectivity of `e` makes the
   underlying ideals equal, and `MaximalSpectrum.ext` gives `M = N`. This
   proves `Subsingleton (MaximalSpectrum B)`, again as a local instance.
4. `IsLocalRing.of_singleton_maximalSpectrum` concludes. Its remaining
   hypothesis `Nonempty (MaximalSpectrum B)` is found by instance search:
   `B` is nontrivial as a subring of the field `L`
   (`SubsemiringClass.nontrivial`), and Mathlib's
   `MaximalSpectrum.instNonemptyOfNontrivial` supplies a maximal ideal.

Inspection in the approved environment reports kind `theorem`, universe
parameters `u, v, w`, and only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Source correspondence and adaptations

The source is Naganori Yamaguchi's ClassFieldTheory at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteIntegralClosure.lean`:
universe line 23, ambient variables 30–31, M245.006 docstring 176–182,
signature 183–186 and proof 187–251. The original name
`ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosure_isLocalRing_of_finite_separable`
becomes the public theorem above with the `Langlands.NYLL` prefix and the exact
closed target. No helper declaration is added, so there are no private lemmas.

The proof keeps the source's ingredients: integrality of the actual integral
closure, the M245.005 fiber subsingleton, `primesOverOrderIsoFiber`, maximality
of contractions of maximal ideals, `IsLocalRing.eq_maximalIdeal` and
`IsLocalRing.of_singleton_maximalSpectrum`. The explicit modifications are:

- The closed-target signature, the explicit independent universes `u, v, w`,
  and the source abbreviations `base.valuationSubring` and `base.maximalIdeal`
  expanded to the actual valuation subring and its maximal ideal.
- The source obtains a prime above `m` by integral lies-over
  (`Ideal.exists_maximal_ideal_liesOver_of_isIntegral`), which needs the
  faithful scalar action from the standalone wrappers
  `CanonicalIntegralClosure.algebraMap_injective` and
  `CanonicalIntegralClosure.faithfulSMul` (M245.001/.002, source lines 33–59).
  Here nonemptiness of the maximal spectrum comes from the nontriviality of
  `B` instead, so neither the lies-over step nor the faithful action is needed
  and those wrappers are not ported.
- The source first proves that `m.primesOver B` is the singleton of the chosen
  prime and then compares each maximal ideal with it. Here two maximal ideals
  are compared directly through `primesOverOrderIsoFiber`.
- The source's `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal` with
  `algebraMap_isIntegral_iff` is replaced by the equivalent current Mathlib
  lemma `Ideal.isMaximal_under_of_isIntegral_of_isMaximal`.
- The NYLL upstream import is replaced by published dependencies and focused
  Mathlib imports.

The accepted M245.005 theorem is imported by Lean name; its proof is not
repeated. Worker 106 supplied no implementation draft, and no other worker's
adapted Lean content was reused.

## Imports and scope

The direct imports are the published `FiniteIntegralClosure.LocalnessStatements`
(the target) and `FiniteIntegralClosure.FiberSubsingletonProof` (the accepted
M245.005 theorem), plus Mathlib's `RingTheory.Ideal.GoingUp` (maximality of
contractions along integral extensions), `RingTheory.LocalRing.MaximalIdeal.Basic`
(`IsLocalRing.eq_maximalIdeal` and `IsLocalRing.of_singleton_maximalSpectrum`)
and `RingTheory.Spectrum.Maximal.Basic` (the nonempty maximal spectrum of a
nontrivial ring). `PrimeSpectrum.primesOverOrderIsoFiber` comes from
`RingTheory.LocalRing.ResidueField.Fiber`, already imported by the target
module.

The only public addition is M245.006's proof. There is no added hypothesis,
global instance, axiom, chosen extension valuation, residue-field finiteness
assumption, or assumed discrete valuation ring structure of `B`. The module
does not construct the maximal ideal data of M245.007, a DVR structure on `B`,
extension valuations, local-field packaging, residue actions, inertia or
reciprocity.

## Attribution and source records

The registered source `external-lean-reuse-snapshots-2026-10-21` has fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The source root is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The verified SHA256 of `FiniteIntegralClosure.lean` is
`43c21425b2c39e7e6e5d2bca1f2b615c5c29e9d91e69d32d079e593df3170094`.

The attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Its ValuedFieldTheory third-party attribution files do not list
`FiniteIntegralClosure.lean`. No applicable erratum was found.

The original copyright and author header is retained verbatim: copyright 2026
Naganori Yamaguchi; authors Naganori Yamaguchi (assisted by OpenAI Codex), under
Apache-2.0. The existing unmodified
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) accompany this adaptation.
Worker 1045 made the modifications listed above on 29 October 2026 and wrote
this Markdown. The approved environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
