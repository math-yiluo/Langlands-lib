# Uniqueness of the finite integral-closure residue fiber

The module proves NYLL M245.005 as the exact published closed proposition
`IntegralClosureBaseMaximalFiberSubsingletonOfFiniteSeparableStatement.{u, v, w}`.
The public theorem is
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosure_base_maximal_fiber_subsingleton_of_finite_separable`.
Its complete unapplied type is that target constant, with independent universe
parameters `u, v, w` in that order and no additional declaration arguments.

The entry module is
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.FiberSubsingletonProof`.
The published target in `FiniteIntegralClosure.LocalnessStatements` and all
published dependencies are used unchanged.

## Data, universes and scalar maps

The target quantifies, in order, over
`(K : Type u) (L : Type w) [Field K] [Field L] [Algebra K L]
[FiniteDimensional K L] (base : CompleteDVF.{u, v} K) [Algebra.IsSeparable K L]`.
The proof introduces exactly these parameters. The value group stored in `base`
lies in `Type v`; its valuation is complete and rank-one discrete as specified
by `CompleteDVF`. None of the three universes is identified with another.

Write `A := base.valuation.valuationSubring`, the actual valuation subring of
`K`, `m := IsLocalRing.maximalIdeal A`, and `B := integralClosure A L`, the
actual Mathlib subalgebra of elements of `L` integral over `A`. The rings
`A` and `B` lie in `Type u` and `Type w`, respectively. The algebra map
`A → L` is the inclusion `A → K` followed by `algebraMap K L`, supplied by
`Algebra.ofSubsemiring`; `algebraMap A B` corestricts this map to the integral
closure, using `Subalgebra.algebra`. The domain structure on `B` is inherited
from its inclusion in the field `L`.

The conclusion is `Subsingleton (PrimeSpectrum (m.Fiber B))`. Here `Ideal.Fiber`
is the actual tensor product `m.ResidueField ⊗[A] B` over these canonical scalar
maps, in `Type (max u w)`. Mathlib's `m.ResidueField` is the residue field of
the localization at `m`; it is canonically isomorphic to `A ⧸ m`, rather than
definitionally equal to that quotient. The canonical map used in the proof is

`f : B →+* m.Fiber B := (Algebra.TensorProduct.includeRight : B →ₐ[A] m.Fiber B)`.

Thus `f b = 1 ⊗ₜ[A] b`. The coercion from this algebra homomorphism to a ring
homomorphism is explicit. No alternative fiber or extension valuation is chosen.

## Implemented proof

The proof first derives `IsNoetherianRing A`, `IsFractionRing A K` and
`IsIntegrallyClosed A` from Mathlib instances. Rank-one discreteness supplies a
discrete valuation ring structure on `A`, hence Noetherianity. A valuation
subring has fraction field `K` and is integrally closed. The same instance
route is used in the accepted `FiniteIntegralClosure.CompletenessProofs` module.
Mathlib's `IsIntegralClosure.finite A K L B` then proves `Module.Finite A B`
from finite dimensionality and separability of `L/K`, together with those
valuation-ring properties and the canonical scalar towers. Instance search
now proves `Algebra.QuasiFinite A B` and `IsArtinianRing (m.Fiber B)`.
These are derived local facts, not assumptions of the theorem or new global
instances.

The private lemma `fiber_includeRight_facts` proves that `f` is surjective and
that `RingHom.ker f = m.map (algebraMap A B)`. For a local ring `R` and an
`R`-algebra `S`, put `I := (IsLocalRing.maximalIdeal R).map (algebraMap R S)`.
The proof constructs the canonical algebra equivalence

`e : (IsLocalRing.maximalIdeal R).Fiber S ≃ₐ[R] S ⧸ I`.

It tensors the inverse of Mathlib's bijective map
`R ⧸ maximalIdeal R → (maximalIdeal R).ResidueField` with the identity on `S`,
commutes the tensor factors, and applies the inverse of
`Algebra.TensorProduct.quotIdealMapEquivTensorQuot`. The computation
`e (f s) = Ideal.Quotient.mk I s` follows from
`quotIdealMapEquivTensorQuot_symm_tmul`. Surjectivity follows from surjectivity
of the quotient map and injectivity of `e`; the same equation and
`Ideal.Quotient.eq_zero_iff_mem` identify the kernel. This avoids assuming that
the mapped ideal is maximal in `B`.

The accepted theorem
`integralClosure_henselianRing_of_finite_separable.{u, v, w} K L base`
gives `HenselianRing B (m.map (algebraMap A B))`. Rewriting by the private
kernel calculation gives `HenselianRing B (RingHom.ker f)`.

The private lemma `lift_idempotent` lifts an idempotent `e` along a surjective
map `f : R →+* S` when `R` is nontrivial and Henselian along its kernel.
Choose `a₀` with `f a₀ = e`, and let `p := X^2-X`. Its image in
`R ⧸ RingHom.ker f` is idempotent, so `p.eval a₀` lies in the kernel. The
polynomial is monic. If `q` is the quotient image of `a₀`, its derivative has
value `q+q-1`, whose square is
`1 + (4*(q*q)-4*q) = 1`, using `q*q=q`. It is therefore a unit in the quotient.
`HenselianRing.is_henselian` produces a root `a` congruent to `a₀` modulo the
kernel. The root equation is `a*a=a`, and congruence gives `f a=e`.
Only the nontrivial case is needed because the main proof applies this to the
domain `B`.

Apply this lifting lemma to any idempotent of `m.Fiber B`. Since `B` is a
domain, `IsIdempotentElem.iff_eq_zero_or_one` says that its lift is zero or one.
Preservation of zero and one by `f` proves that the original fiber idempotent
is zero or one.

Finally, the private lemma `spectrum_subsingleton_of_trivial_idempotents` uses
Mathlib's discrete topology on the prime spectrum of an Artinian ring. A
singleton `{P}` is clopen, so
`PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen` represents it as
`basicOpen e` for an idempotent `e`. If `e=0`, the singleton is empty, which
contradicts membership of `P`. If `e=1`, it is the whole spectrum, so every
other prime `Q` equals `P`. This proves the required subsingleton without an
assumption of nonemptiness of the fiber spectrum.

## Source correspondence and adaptations

The source is Naganori Yamaguchi's ClassFieldTheory at commit
`fbd320cd8b1b06487c58227e92eb135794267709`. All paths in the following table are
under `Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/` in that snapshot.
The adapted names are in the namespace of the public theorem above; all three
helpers are private.

| Source unit and original name | Location | Implementation here |
| --- | --- | --- |
| M245.005, `integralClosure_base_maximal_fiber_subsingleton_of_finite_separable` | `FiniteIntegralClosure.lean`, universe line 23, ambient variables 30–31, docstring 117–121, signature 122–127, proof 128–174 | Public theorem of the same name with the `Langlands.NYLL` prefix and exact closed target |
| M192.001, `primeSpectrum_subsingleton_of_isArtinianRing_of_idempotents_trivial` | `IntegralClosure.lean`, 36–65 | `spectrum_subsingleton_of_trivial_idempotents`, the same clopen-singleton argument with shorter names and a simplified empty-set contradiction |
| M192.002, `maximalIdeal_fiber_includeRight_surjective` | `IntegralClosure.lean`, 67–86 | Surjectivity part of `fiber_includeRight_facts`, obtained through the quotient equivalence instead of the source's unit-scaling argument |
| M192.003, `maximalIdeal_fiber_includeRight_ker_eq_maximalIdeal_map` | `IntegralClosure.lean`, 88–129 | Kernel part of `fiber_includeRight_facts`, retaining the source equivalence and its computation on `includeRight` |
| M104.001–.004, `idempotentPolynomial_monic`, `idempotentPolynomial_eval_mem_of_quotient_idempotent`, `idempotentPolynomial_derivative_eval_isUnit_of_quotient_idempotent`, `exists_idempotent_lift_of_surjective_henselianRing_ker` | `Henselian.lean`, 28–128 | `lift_idempotent`, with the three polynomial calculations inlined, the derivative inverse equation proved once, and the unused subsingleton-ring branch omitted |

The main proof follows the source's finite-Artinian-fiber and idempotent-lifting
route. Its changes are the closed-target signature, explicit independent
universes, expanded actual valuation subring and maximal ideal, direct Mathlib
valuation-ring instances in place of NYLL wrappers, local `have` instances,
the combined private fiber-map lemma, the restricted private lifting lemma,
and shorter final uses of the ring map's zero and one equations. It imports
the accepted Henselianity theorem by Lean name; it does not port that proof or
the source's generic helper modules. Worker 106 supplied no implementation
draft, and no other worker's adapted Lean content was reused.

## Imports and scope

The direct imports are the published `FiniteIntegralClosure.LocalnessStatements`
and `FiniteIntegralClosure.CompletenessProofs`, plus Mathlib's
`RingTheory.QuasiFinite.Basic`, `RingTheory.Spectrum.Prime.Topology` and
`RingTheory.TensorProduct.Quotient`. The completeness module supplies the
needed finite-integral-closure theorem and valuation-ring instances through
its focused Mathlib imports; it also provides `HenselianRing`. The three extra
Mathlib modules supply the Artinian fiber instances, discrete Artinian spectrum
and clopen-idempotent correspondence, and tensor-quotient equivalence.

The only public addition is M245.005's proof. There is no added hypothesis,
global instance, axiom, extension valuation, residue-field finiteness assumption,
or assumed localness or discrete valuation ring structure of `B`. In particular,
this module does not prove M245.006, later maximal-ideal data, extension valuation
existence or uniqueness, local-field packaging, inertia or reciprocity.

## Attribution and source records

The registered source `external-lean-reuse-snapshots-2026-10-21` has fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The source root is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The verified SHA256 values are:

| Original file | SHA256 |
| --- | --- |
| `FiniteIntegralClosure.lean` | `43c21425b2c39e7e6e5d2bca1f2b615c5c29e9d91e69d32d079e593df3170094` |
| `IntegralClosure.lean` | `b0309db3073ffb278f6558c442acc19ab72ba76ed32ce4d88a63b953e65c86c2` |
| `Henselian.lean` | `cce4a6ecfed6076732a5041ad23935a638de6eb5c3c35287d289c8b1717e0cf2` |

The attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Its ValuedFieldTheory third-party source table lists none of these three files.
The published M245 partition records no compatibility patch, and no applicable
erratum was found in the project lookup.

The original copyright and author header is retained verbatim: copyright 2026
Naganori Yamaguchi; authors Naganori Yamaguchi (assisted by OpenAI Codex), under
Apache-2.0. The existing unmodified
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) accompany this adaptation.
Worker 122 made the modifications listed above on 29 October 2026 and wrote
this Markdown. The approved environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
