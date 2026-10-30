# Renard A.IX: finite closure and abelianness of supported objects

Authors: Worker 6 and Worker 122. Worker 6 authored the initial paired draft;
Worker 122 rechecked the source, published interfaces and complete declarations
and prepared this submission. This is a proposition-target unit, with no closure
or abelianness theorem proved here.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, A.IX, printed page 268 /
PDF page 274. The registered original is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
The complete page was read as extracted text and visually checked against
the original. Renard assumes a Grothendieck category satisfying his AB6
and a subset `S` of its simple-object isomorphism classes. He defines
the full subcategory `M_S` by requiring that every simple subquotient
belong to `S`, then states that it is abelian and stable under
subquotients, extensions and colimits.

Worker 122 also read the original definitions and statements in A.VI.3,
printed263–264 / PDF269–270. Worker 6 read the neighboring A.IX material
on PDF273–275 in the preceding source audit. The supplementary registered
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
is a different edition. Its Appendix A pages PDF18–19 were read by both authors.
The old-page310 letter correction concerns the later supported sum and is
already present in the 2026 text. No correction to the closure assertion
is claimed from that comparison. The public
`notes/renard/appendix-a-corrections.md` diagnoses a different, insufficient
abelian-subcategory criterion at A.VI.1; it does not disprove the
supported-subcategory assertion here.

No dedicated source errata note was present at the inspected workspace, project
or pinned Library paths. On 29 October 2026, Worker 122 rechecked the
[author’s books page](https://perso.pages.math.cnrs.fr/users/david.renard/).
Its bytes match registered snapshot `renard-author-page-2026-10-26`, SHA256
`143092e92be11be1b9c5a03bfc1e9e4538edb45f9a67d5fc8cc474b7b6dcd580`.
The books section links a corrected 2026 French text and explicitly labels
the separate errata as for the 2010 edition; no separate 2026 errata link
appears there. This is a bounded errata check, not an exhaustive claim.

## Actual objects and hypotheses

Every declaration is in `Langlands.Renard`. The common parameters are
`C : Type u`, `[Category.{v} C]`, and `[Abelian C]`, with independent
family universe `w`, Hom universe `v`, and object universe `u`.
Every component retains `IsSourceGrothendieck.{w} C → SourceAB6 C` and
quantifies over every `S : Set (ObjectClass C)` with
`S ⊆ simpleClasses C`. There is no smallness, well-poweredness,
generator, finite-length or concrete-category premise.

The imported definitions are unchanged. `ObjectClass C` is the actual
isomorphism quotient of objects, and `simpleSubquotientClasses X`
contains the classes of all simple cokernels of nested subobjects of
`X`, including when `X` has infinite length.
`HasSimpleSupport S X` is `simpleSubquotientClasses X ⊆ S`.
`simpleSupportObjects S` is this actual object predicate, and
`SimpleSupportSubcategory S` is its actual Mathlib full subcategory.
`simpleSupportInclusion S` is its actual full and faithful inclusion
into `C`. No alternative category or functor is supplied.

## Proposition targets

| Declaration | Conclusion after the common source hypotheses |
| --- | --- |
| `SimpleSupportSerreStatement C` | `(simpleSupportObjects S).IsSerreClass` |
| `SimpleSupportFiniteProductsStatement C` | `(simpleSupportObjects S).IsClosedUnderFiniteProducts` |
| `SimpleSupportAbelianStatement C` | An actual abelian structure on `SimpleSupportSubcategory S` whose preadditive structure is the inherited one |
| `SimpleSupportInclusionExactStatement C` | `PreservesFiniteLimits (simpleSupportInclusion S) ∧ PreservesFiniteColimits (simpleSupportInclusion S)` |
| `SimpleSupportFiniteClosureStatement C` | The conjunction of the preceding four targets, in that order |

All five are `def` declarations returning `Prop`.

Mathlib's actual `ObjectProperty.IsSerreClass` is a proposition containing
zero containment, closure under every ambient monomorphism, closure under
every ambient epimorphism, and closure under short exact sequences.
Specifically, `ContainsZero` asserts an actual zero object with the
property. `IsClosedUnderSubobjects` says that for every mono `X ⟶ Y`,
support of `Y` implies support of `X`. `IsClosedUnderQuotients` says that
for every epi `X ⟶ Y`, support of `X` implies support of `Y`.
`IsClosedUnderExtensions` says that support of the endpoints of any
actual short exact short complex implies support of its middle object.
Together the mono and epi clauses include every actual subquotient.
They also imply invariance under actual isomorphisms.

`IsClosedUnderFiniteProducts` is the existing Mathlib proposition for
closure under every finite discrete limit. It is an internal consequence
of the zero and extension assertions, using finite biproducts in the
ambient abelian category. Making it explicit prevents reuse of the
incorrect A.VI.1 criterion that omits finite-product closure.

The abelian target uses the inherited full-subcategory category and asserts
`∃ a : Abelian (SimpleSupportSubcategory S),
a.toPreadditive = Preadditive.fullSubcategory (simpleSupportObjects S)`.
`Abelian` itself contains preadditive data, so the equality explicitly
requires that data to be the restriction of the ambient addition.
Existential quantification keeps the target Prop-valued. The final inclusion target
expresses exactness through actual finite-limit and finite-colimit
preservation. These two clauses jointly assert an abelian full
subcategory whose actual inclusion is exact; they do not merely supply
an unrelated abelian category equivalent to it.

## Provenance and proof boundary

Subobject, quotient and extension closure and abelianness are the source
assertions. The Serre-class packaging, explicit zero clause,
finite-product clause and preservation clause are internal formulations
or consequences of these assertions. They are not separately numbered
theorems in Renard and are not assumptions supplying the desired result.

The existing public mono/epi transport lemmas and clause (i) for simple
subquotients in
`Langlands.CategoryTheory.Renard.SimpleSubquotientSubobjectQuotient`
provide a proof route. Closure under extensions can use the actual
short-exact cokernel comparison. The corrected Mathlib
`CategoryTheory.Abelian.Subcategory` criterion requires zero, kernels,
cokernels and finite products; these must be established for the actual
support predicate before it supplies an abelian structure.

No such proof is part of this unit. Arbitrary coproduct/colimit closure,
support and maximality of `E_S`, Hom orthogonality, splitting and product
decomposition remain separate tasks. The existing sum proof tasks retain
their owners. Development elaboration is not independent acceptance or
publication.
