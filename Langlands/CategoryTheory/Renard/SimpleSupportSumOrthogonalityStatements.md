# Renard A.IX: disjointness of the full supported sums

This pair states the zero-intersection and binary direct-sum inclusion
consequences in Renard A.IX for the actual sums of all supported subobjects.
It supplies one proposition target,
`Langlands.Renard.SimpleSupportSumOrthogonalityStatement`.
It contains no proof of that target.

## Source correspondence

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The assertions are in A.IX, printed page 268 / PDF page 274, after the
definition of the supported subcategory and its full supported sum.
The source context and subobject conventions are in A.VI.2–3,
printed pages 263–264 / PDF pages 269–270.

The complete A.IX page and these conventions were read in the source audit
behind the [A.IX progress map](../../../notes/renard/category-decomposition-progress.md).
That audit also checked the registered 2010-edition corrections at PDF
pages 18–19: the old-page-310 letter correction is already incorporated
in the 2026 supported-sum passage. This is a bounded comparison with the
older corrections, not a claim of exhaustive errata absence.

For disjoint subsets of the simple classes, Renard states that the
corresponding sums have zero intersection and that their direct sum embeds
in the ambient object. The Lean target expresses these as the conjunction,
in this order:

1. `simpleSupportSum S X ⊓ simpleSupportSum T X = ⊥` in the actual lattice
   `Subobject X`;
2. `Mono (biprod.desc (simpleSupportSum S X).arrow
   (simpleSupportSum T X).arrow)`, using the actual inclusions into `X`.

The second clause is the categorical realization of the source inclusion.
It does not assert that the map is epi or invertible. The subsets need
not cover all simple classes, and no splitting premise is supplied.

## Complete hypotheses and universes

The ambient data are arbitrary `C : Type u`, `[Category.{v} C]` and
`[Abelian C]`. The source coproduct universe `w`, Hom universe `v` and object
universe `u` remain independent.

The target first quantifies `hG : IsSourceGrothendieck.{w} C` and installs
`HasCoproducts.{w} C` from `hG.1`. It then assumes `SourceAB6 C`,
arbitrary `S T : Set (ObjectClass C)`, both inclusions
`S ⊆ simpleClasses C` and `T ⊆ simpleClasses C`, and `Disjoint S T`.
Here `ObjectClass C` is the actual isomorphism-class quotient and
`simpleClasses C` represents the source's simple classes.

For every actual ambient object `X`, the target separately requires
`Small.{w} (simpleSupportSubobjects S X)` and
`Small.{w} (simpleSupportSubobjects T X)`. Each of these full families
contains every subobject whose underlying object has its indicated
simple support. There is no finite-length or chosen-subfamily
restriction. For each full family, the target installs the particular
`HasCoproductsOfShape` instance obtained by
`hasCoproductsOfShape_of_small.{w}` from the source coproducts.
Both occurrences of `simpleSupportSum` use those derived instances.

The sum is the published actual subobject obtained as the image of the
coproduct-inclusion map for the full family. Its intrinsic least-upper-bound
laws alone do not imply that it is supported. The family-size conditions
are the formal size bookkeeping needed to use the source-sized support
theorem at both sums. This target does not discharge those conditions or
claim a new size bridge.

The source Grothendieck convention is the one defined in
[RenardGrothendieckAxioms](../RenardGrothendieckAxioms.md):
the source coproduct and directed-subobject-sum distributivity conditions,
without a generator clause.
[LocallyFiniteType](LocallyFiniteType.md) defines `SourceAB6` using all
finite-type subobjects. No similarly named external convention is silently
substituted. No well-poweredness, chosen representatives, concreteness,
generator, finite length, finite type of `X`, or relation among `w`, `v`
and `u` is added.

In particular, the statement does not assume coproducts at `max u v`.
That enlarged global hypothesis forces the Hom types to be subsingletons,
as explained in the published [supported-sum companion](SimpleSupportSum.md).
The two explicit smallness premises preserve the independent source size.
Empty supports and the zero ambient object are included.

## Existing results and remaining proof

[SimpleSupportSumStatements](SimpleSupportSumStatements.md) already states
support of each actual full sum, with precisely its own family-size
premise. [SimpleSupportOrthogonalityStatements](SimpleSupportOrthogonalityStatements.md)
states zero intersection and monicity for arbitrary actually supported
subobjects. Those targets already have published proofs in
[SimpleSupportSumProof](SimpleSupportSumProof.md) and
[SimpleSupportOrthogonality](SimpleSupportOrthogonality.md).

The intended later proof applies the published support theorem separately
to the two sums, then specializes the published arbitrary-supported-subobject
results. A private composition diagnostic has checked that these interfaces
compose with independent universes and both smallness premises. This
statement pair neither imports that diagnostic nor exports its proof.
It introduces no support certificate, orthogonality assumption or
conclusion-equivalent hypothesis.

The new target records the literal full-sum specialization that those
earlier units explicitly reserved. Independent statement acceptance and
publication must precede a separate exact-target proof task. This pair
does not change the earlier generic statements or establish additional
closure, functor, splitting or category-decomposition results. It does
not declare A.IX or the whole-book program complete.
