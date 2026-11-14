# NYLL M039: the finite norm quotient — statement targets

The paired Lean file adapts six theorem statements from Naganori Yamaguchi's
ClassFieldTheory at pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean`,
SHA-256
`f541cbe9d1f0a01b867d7339fc7ef0eb830bd9bf799ceaadfb6506c4bb334da7`.
The source is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Its registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum was found in the available project notes.

## Source correspondence

Every original name has prefix `ClassFormation.` and every adapted name has
prefix `Langlands.NYLL.ClassFormation.`.

| Unit | Source name | Statement lines | Original proof lines | Adapted Prop definition |
| --- | --- | --- | --- | --- |
| M039.010 | `finiteNormClass_nsmul` | 124–132 (docstring 124, `@[simp]` 125) | 133 | `finiteNormClass_nsmulStatement` |
| M039.012 | `finiteNormClass_eq_zero_iff` | 147–155 (docstring 147, `@[simp]` 148) | 156–157 | `finiteNormClass_eq_zero_iffStatement` |
| M039.013 | `finiteNormClass_surjective` | 159–164 (docstring 159) | 165–170 | `finiteNormClass_surjectiveStatement` |
| M039.014 | `FiniteNormQuotient.induction_on` | 172–180 (docstring 172, `@[elab_as_elim]` 173) | 181–182 | `FiniteNormQuotient.induction_onStatement` |
| M039.016 | `finiteNormQuotientLift_finiteNormClass` | 196–207 (docstring 196, `@[simp]` 197) | 208 | `finiteNormQuotientLift_finiteNormClassStatement` |
| M039.017 | `finiteNormQuotient_degree_nsmul_eq_zero` | 210–216 (docstring 210–212) | 217–223 | `finiteNormQuotient_degree_nsmul_eq_zeroStatement` |

The enclosing source context is `namespace ClassFormation` (line 20),
`open KummerTheory` (line 22), `open CyclicCohomology` (line 24),
`noncomputable section` (line 28), `section finiteNorms` (line 30) and the
group variables at line 33. Each theorem becomes a `def` returning `Prop`
whose explicit and implicit binders are the source hypotheses in source
order, and whose body is the source conclusion, after the namespace change
and abbreviation expansion below. The original proofs are separate
obligations.

## Complete parameters and assertions

Every target begins with implicit `{G : IntegralRepGroupType}`, `[Group G]`
and `[TopologicalSpace G]` (`IntegralRepGroupType` is `Type 0`; the
representation carrier universe is arbitrary). Except for M039.017, the
common telescope is then `A : Rep ℤ G`, `K L : ClosedSubgroup G`,
`hLK : L.toSubgroup ≤ K.toSubgroup` and the instance
`[Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]`. The data
`finiteNormSubgroup`, `FiniteNormQuotient` with its `AddCommGroup` instance
`finiteNormQuotientAddCommGroup`, `finiteNormClass` and
`finiteNormQuotientLift` are those of [`Definitions.md`](Definitions.md).

- `finiteNormClass_nsmulStatement`: after the common telescope, explicit
  `n : ℕ` and `a : ambientFixedAddSubgroup A K`; assertion
  `finiteNormClass A K L hLK (n • a) = n • finiteNormClass A K L hLK a`.
- `finiteNormClass_eq_zero_iffStatement`: then explicit
  `a : ambientFixedAddSubgroup A K`; assertion
  `finiteNormClass A K L hLK a = 0 ↔ a ∈ finiteNormSubgroup A K L hLK`,
  i.e. the class of `a` vanishes iff `a` is a norm from `A_L`.
- `finiteNormClass_surjectiveStatement`: no further binders; assertion
  `Function.Surjective (finiteNormClass A K L hLK)`.
- `FiniteNormQuotient.induction_onStatement`: then implicit
  `{motive : FiniteNormQuotient A K L hLK → Prop}`, explicit
  `q : FiniteNormQuotient A K L hLK` and the hypothesis
  `h : ∀ a, motive (finiteNormClass A K L hLK a)`; its body is the source
  conclusion `motive q`. The hypothesis `h` is a binder of the Prop-valued
  definition, so the target applied to `A K L hLK q h` is exactly the source
  theorem's conclusion; the definition body does not mention `h`, and the
  unused-variables linter is disabled for this declaration only so that the
  source name `h` is retained.
- `finiteNormQuotientLift_finiteNormClassStatement`: telescope
  `{B : Type*} [AddCommGroup B]` (after the group variables, before `A`, as in
  the source), the common telescope, then explicit
  `f : ambientFixedAddSubgroup A K →+ B`,
  `hf : finiteNormSubgroup A K L hLK ≤ f.ker` and
  `a : ambientFixedAddSubgroup A K`; assertion
  `finiteNormQuotientLift A K L hLK f hf (finiteNormClass A K L hLK a) = f a`.
  It has an independent universe parameter for `B`.
- `finiteNormQuotient_degree_nsmul_eq_zeroStatement`: explicit
  `A : Rep ℤ G`, `E : DegreeData.FiniteAbstractExtension G` and
  `q : FiniteNormQuotient A E.base E.field E.below`; assertion
  `(E.degree : ℕ) • q = 0`, that the positive degree `[L : K]` of the finite
  abstract extension, coerced to `ℕ`, kills every class. As in the source,
  the finiteness instance for `FiniteNormQuotient A E.base E.field E.below`
  is found by instance search, from the published
  `DegreeData.FiniteAbstractExtension.representedQuotientFinite`
  (source `Degree/Fields.lean`, lines 646–652).

## Reused objects and modifications

The imports supply published data by Lean name:
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.Definitions`
(the M039 data above, `relativeNorm` and `ambientFixedAddSubgroup`) and
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteExtension.Definitions`
(`DegreeData.FiniteAbstractExtension` M010.065, its `degree` M010.085 and the
instance `representedQuotientFinite`).

Source `CyclicCohomology.extensionSubgroup K L hLK` (M004.002,
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean`, lines 47–54,
SHA-256 `06d33a5e35d45458927e2ac18fe7103bc061dec851162110347e847d7d78f0c8`)
is an abbreviation with body `L.toSubgroup.subgroupOf K.toSubgroup`; each
occurrence is replaced by that exact Mathlib term. The inclusion parameter
`hLK` remains in every telescope.

Worker 96 made only the following adaptations on 14 November 2026:

1. Prefix the namespace by `Langlands.NYLL`; import the two focused
   published modules instead of the original imports. Drop the unused
   `open CyclicCohomology` and `universe u`.
2. Expand `extensionSubgroup` by its exact body, with parentheses.
3. Convert each theorem into the listed Prop-valued `def` with the
   `Statement` suffix, keeping every source hypothesis, binder kind and order
   and the entire conclusion. Omit the proofs and the `@[simp]` and
   `@[elab_as_elim]` attributes, which belong to proved theorems. Disable
   the unused-variables linter for `FiniteNormQuotient.induction_onStatement`
   only.
4. Keep `noncomputable section` and `section finiteNorms`, replace the module
   introduction with an extraction notice, and mark the docstrings as
   targets.

The unlisted source theorems M039.007–M039.009 and M039.011 are not used by
these targets and are not ported here. No instance or helper declaration is
introduced.

## Development verification and scope

The module compiles with zero errors and warnings in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean v4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Focused inspection of each of the
six targets succeeds and reports `statement_returns_prop = true`.

A private probe reconstructs the source data with the original
`extensionSubgroup` instance binders, restates the six source assertions over
that reconstruction, and verifies equality of each entire dependent function
with the adapted target by `rfl` (for the lift target at two arbitrary
independent universes). The probe supplies no public declaration.

These are statement targets in the NYLL abstract-field model; their proofs
belong to separate `lean.proof@1` tasks after publication. The host
class-formation, cup, transfer, Tate and reciprocity obligations remain with
their existing owners.

## Attribution

The original copyright, author and Apache-2.0 header is retained verbatim.
The existing Library files `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are retained, with respective SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The Lean modification notice and this Markdown identify every adaptation.
