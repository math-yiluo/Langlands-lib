# The maximal ideal of the finite integral closure

The module defines NYLL M245.007, the maximal ideal of the integral closure of
the valuation ring of a complete discretely valued field in a finite separable
extension. The only declaration is the noncomputable definition
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension.CanonicalIntegralClosure.maximalIdeal.{u, v, w}`.
It is structural data, not a theorem or a proposition target.

The entry module is
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.MaximalIdeal`.
All published dependencies are used unchanged.

## Signature, universes and data

The complete unapplied type of the definition is

```
∀ {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] (base : CompleteDVF.{u, v} K) [Algebra.IsSeparable K L],
  Ideal (integralClosure base.valuation.valuationSubring L)
```

The universe parameters are `u, v, w`, in that order. `u` is the universe of
the base field `K`, `v` the universe of the value group stored in `base`, and
`w` the universe of the extension field `L`. None of them is identified with
another, and none is restricted to `Type 0`. These are exactly the source
parameters: `K` and `L` are implicit, as in the source's ambient `variable`
lines, `base` is explicit, and every structure argument is instance-implicit.
There is no other argument. In particular there is no `IsLocalRing` premise,
no assumed upstairs maximal ideal, no `IsDiscreteValuationRing` structure, no
chosen extension valuation, no `Module.Finite` hypothesis and no extension
record.

Write `A := base.valuation.valuationSubring` and `B := integralClosure A L`.

- `base : CompleteDVF.{u, v} K` packages a valuation on `K` with values in a
  value group in `Type v`, complete and rank-one discrete. `A` is Mathlib's
  actual valuation subring of `K` for this valuation. It is a ring in `Type u`
  and is local by Mathlib's valuation-subring instance.
- The scalar map `A → L` is the inclusion of `A` into `K` followed by
  `algebraMap K L`. It is Mathlib's `Algebra.ofSubsemiring` instance for the
  subring `A` of `K`.
- `B` is Mathlib's actual subalgebra `integralClosure A L` of `L`: the elements
  of `L` that are integral over `A`. It is a ring in `Type w`. Its ring
  structure is the subalgebra structure (`Subalgebra.toCommSemiring` and its
  ring refinements). Its scalar map `A → B` corestricts `A → L` to `B`
  (`Subalgebra.algebra`), so `((algebraMap A B a : B) : L) = algebraMap K L a`
  holds by `rfl`.
- The result type is `Ideal B` for this actual ring.

The source writes `base.valuationSubring`. In the Library this spelling is the
published projection abbreviation in `Complete.Projections`, which reduces to
`base.valuation.valuationSubring`. The statement uses the latter, the same
spelling as the published M245.006 statement, so the module neither imports
nor introduces an alias. A private check confirms that
`Ideal (integralClosure base.valuationSubring L)` and the result type are equal
by `with_reducible rfl`.

## Implemented construction

The body has two steps.

1. `letI : IsLocalRing B :=
   integralClosure_isLocalRing_of_finite_separable.{u, v, w} K L base`.
   The published M245.006 theorem proves the closed proposition
   `IntegralClosureIsLocalRingOfFiniteSeparableStatement.{u, v, w}`. That
   proposition quantifies explicitly over `K` and `L`, so the theorem is applied
   to `K`, `L` and `base` as explicit arguments, with the universes passed
   unchanged. The instance arguments are then found from the definition's own
   binders. The witness is installed only inside the body. No global instance
   is added, and the localness proof is not repeated.
2. `IsLocalRing.maximalIdeal B`. This is Mathlib's canonical maximal ideal of a
   local ring: the ideal whose carrier is the set `nonunits B` of non-units of
   `B`. It is not chosen from an existence proof.

So the definition is the ideal of non-units of the actual integral closure. Its
value is `@IsLocalRing.maximalIdeal B _ (integralClosure_isLocalRing_of_finite_separable.{u, v, w} K L base)`.
The localness witness is a proof, so by proof irrelevance the value is
definitionally the same for any other `IsLocalRing B` witness.

## Checks

The approved environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Inspection of the declaration
reports kind `definition`, universe parameters `u, v, w` and only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`. The definition is
noncomputable, has default (semireducible) transparency and is not an
instance.

Private checks, which are not part of the module, confirm the following.

- The complete unapplied type is the one displayed above, binder by binder and
  with the binder kinds stated there.
- After `delta`, the definition equals
  `@IsLocalRing.maximalIdeal B _ (integralClosure_isLocalRing_of_finite_separable.{u, v, w} K L base)`
  by `with_reducible rfl`. The equation lemma gives the same equality. For an
  arbitrary witness `h : IsLocalRing B`, the definition equals
  `@IsLocalRing.maximalIdeal B _ h` by `with_reducible rfl` as well.
- The stored value uses the accepted theorem by name, together with
  `IsLocalRing.maximalIdeal`.
- Membership in the ideal is equivalent to being a non-unit of `B`. Every
  maximal ideal of `B` equals the definition, and the definition is maximal.
  These checks use the local witness and Mathlib's `IsLocalRing` lemmas.
- Without the local witness, instance search finds no `IsLocalRing B`
  instance.

When `L` cannot be inferred from the expected type, it must be supplied as
`(L := L)`. This is because `L` is implicit, as it is in the source.

## Source correspondence and adaptations

The source is Naganori Yamaguchi's ClassFieldTheory at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteIntegralClosure.lean`.
The universe line is 23, the ambient variables are on lines 30–31, the
M245.007 docstring is on lines 253–254 and the declaration is on lines
255–262, starting at line 255. The original name
`ValuationTheory.DiscreteValuationField.ValuedExtension.CanonicalIntegralClosure.maximalIdeal`
becomes the definition above with the `Langlands.NYLL` prefix. The source
docstring is kept. Only its reference to "the finite separable localness
theorem above" now names M245.006, because that theorem lives in a separate
module.

The source body is the same two-step construction: a local `letI` of the
localness theorem, then `IsLocalRing.maximalIdeal` of the actual integral
closure. The explicit modifications are:

- The ambient `universe` and `variable` lines become binders of the
  definition, with explicit universe parameters `.{u, v, w}`. Binder order and
  binder kinds are unchanged.
- The source abbreviation `base.valuationSubring` is expanded to
  `base.valuation.valuationSubring`.
- The source applies the localness theorem as
  `integralClosure_isLocalRing_of_finite_separable (K := K) (L := L) base`.
  The published theorem proves a closed proposition whose `K` and `L` are
  explicit, so it is applied as
  `integralClosure_isLocalRing_of_finite_separable.{u, v, w} K L base`.
- The source's `noncomputable section` is replaced by marking the definition
  itself `noncomputable`.
- The upstream import of `FiniteExtension.Core` is replaced by the focused
  imports below.

Worker 106 supplied routing only, no implementation draft. No other worker's
adapted Lean content was reused.

## Imports and scope

The direct imports are:

- the published `FiniteIntegralClosure.LocalnessProof`, for the accepted
  M245.006 theorem. Through the published `LocalnessStatements` module, this
  also provides `CompleteDVF`, `integralClosure`, the finiteness and
  separability classes, and `IsLocalRing`;
- Mathlib's `RingTheory.LocalRing.MaximalIdeal.Defs`, for
  `IsLocalRing.maximalIdeal`.

`FiniteExtension.Core` is not ported.

The only public addition is this definition. There is no added hypothesis,
global instance, axiom, theorem or alias. The module does not state or prove the
later source results: M245.008 (the image of the base maximal ideal lies in this
ideal), M245.009 (that image is nonzero), M245.010 (`B` is not a field),
M245.011 (`B` is a discrete valuation ring), or any extension-valuation,
completeness, residue-field, inertia or reciprocity statement. Those are
separate statement and proof work.

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
`FiniteIntegralClosure.lean`, and NOTICE has no source-specific entry for it.
No applicable erratum was found.

The original copyright and author header is kept verbatim: copyright 2026
Naganori Yamaguchi; authors Naganori Yamaguchi (assisted by OpenAI Codex), under
Apache-2.0. The existing unmodified
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) accompany this adaptation.
Worker 1045 made the modifications listed above on 30 October 2026, recorded
them in the Lean header, and wrote this Markdown.
