# Renard A.IX: proof of finite closure and abelianness of supported objects

Author: Worker 1052.

This module proves `Langlands.Renard.simpleSupportFiniteClosure`, whose
entire type is

```lean
theorem simpleSupportFiniteClosure
    (C : Type u) [Category.{v} C] [Abelian C] :
    SimpleSupportFiniteClosureStatement.{w} C
```

with independent universe parameters `w`, `v` and `u`. The target is the
unchanged published proposition in
`Langlands.CategoryTheory.Renard.SimpleSupportFiniteClosureStatements`.
It is the ordered conjunction of `SimpleSupportSerreStatement`,
`SimpleSupportFiniteProductsStatement`, `SimpleSupportAbelianStatement` and
`SimpleSupportInclusionExactStatement`. Each component keeps the source
hypotheses `IsSourceGrothendieck.{w} C`, `SourceAB6 C` and
`S ⊆ simpleClasses C`, and quantifies over every
`S : Set (ObjectClass C)`. The published statement pair and everything it
imports are unchanged. Besides the statement module, the proof imports the
published `Langlands.CategoryTheory.Renard.SimpleSubquotientSubobjectQuotient`
and Mathlib's `Mathlib.CategoryTheory.Preadditive.LeftExact`. No new file
besides this pair is added. The approved Lean service reported the axioms `propext`,
`Classical.choice` and `Quot.sound`; there are no proof holes.

## Source and provenance

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1052 read A.IX, printed page 268 / PDF page 274, as extracted text
from that file. Renard states without proof that `M_S`, the full subcategory
of objects whose irreducible subquotients lie in `S`, is an abelian
subcategory stable under subquotients, extensions and colimits. Worker 1052
also read A.VI.3, printed pages 263–264 / PDF pages 269–270. There Renard
defines `JH(M)` as the set of simple subquotients and proves
`JH(M) = JH(M') ∪ JH(M/M')` for a subobject `M' ⊂ M` (Lemma (i)) and
`JH(M) = ∅` if and only if `M = 0` (Lemma (ii)).

The route below follows Renard's implicit argument for the finite part of
the assertion. Subquotient closure is transport of simple subquotients
along monomorphisms and epimorphisms. Extension closure is Lemma (i) applied
to the image of the first map of a short exact sequence. Only the trivial
direction of Lemma (ii) is used: a zero object has no simple subquotient.
Finite-product closure, the identification of the abelian structure with the
inherited preadditive structure, and exactness of the inclusion are the
internal realization clauses of the published target. They are obtained
from Mathlib's full-subcategory machinery, not from Renard. Colimit closure
is not part of this unit.

None of the three source hypotheses is used. Every proved closure property
holds for every set `S` of object classes in every abelian category. The
Grothendieck and AB6 hypotheses in Renard matter only for the converse
direction of Lemma (ii) and for colimits, neither of which is needed here.

## Helper lemmas and instances

All declarations are in `Langlands.Renard`, for `C : Type u` with
`[Category.{v} C] [Abelian C]`, and, where relevant, `S : Set (ObjectClass C)`.

- `simpleSubquotientClasses_eq_empty_of_isZero`: if `IsZero Z`, then
  `simpleSubquotientClasses Z = ∅`. A simple subquotient is a simple
  cokernel of `Subobject.ofLE A B h` for subobjects `A ≤ B` of `Z`. The
  underlying object of `B` is zero because `B.arrow` is a monomorphism into
  a zero object. The cokernel is then zero because the cokernel projection
  is an epimorphism from the zero object `B` onto it. That contradicts
  `Simple.not_isZero`.
- `simpleSubquotientClasses_subset_union_of_shortExact`: for a short
  complex `S : ShortComplex C` with `hS : S.ShortExact` (in this helper `S`
  names the short complex, not a set of classes), the simple subquotient
  classes of `S.X₂` lie in those of `S.X₁` union those of `S.X₃`.
  Put `P := Subobject.mk S.f`. The published
  `simpleSubquotientClasses_subset_union` gives the classes of `P` union the
  classes of `cokernel P.arrow`. The underlying object of `P` is isomorphic
  to `S.X₁` by `Subobject.underlyingIso`. An isomorphism
  `cokernel P.arrow ≅ S.X₃` is the composite of `cokernelEpiComp` (removing
  the isomorphism `(Subobject.underlyingIso S.f).inv`), `cokernelIsoOfEq`
  with `Subobject.underlyingIso_arrow`, and the uniqueness of cokernels
  between `cokernelIsCokernel S.f` and `hS.gIsCokernel`. The published
  `simpleSubquotientClasses_subset_of_mono`, applied to the two isomorphisms
  above, finishes the proof.
- Instance `simpleSupportObjects_isSerreClass`: the four fields of Mathlib's
  `ObjectProperty.IsSerreClass` for the actual `simpleSupportObjects S`.
  For `exists_zero`, the chosen zero object `0` has empty simple support by
  the first helper. For `prop_of_mono` and `prop_of_epi`, the published
  `simpleSubquotientClasses_subset_of_mono` and
  `simpleSubquotientClasses_subset_of_epi` hold for every ambient
  monomorphism and epimorphism. For `prop_X₂_of_shortExact`, the second
  helper puts the classes of the middle term inside the union of the two
  supported end terms.
- Instance `simpleSupportObjects_isClosedUnderBinaryProducts`: for a
  binary limit presentation, the limit point is isomorphic to the ambient
  binary biproduct of its two supported factors. This uses
  `IsLimit.conePointUniqueUpToIso`, `BinaryBiproduct.isLimit` and
  `diagramIsoPair`. Mathlib's `ObjectProperty.prop_biprod` shows that a
  property closed under extensions contains `X₁ ⊞ X₂` whenever it contains
  `X₁` and `X₂`, via the split short exact sequence of the biproduct. The
  extension closure is the Serre-class instance above, and `prop_of_iso`
  transports the result to the limit point.
- Instance `simpleSupportObjects_isClosedUnderFiniteProducts`: Mathlib's
  `ObjectProperty.IsClosedUnderFiniteProducts.mk'`, from zero containment
  (a Serre-class field) and binary-product closure.
- `simpleSupportSubcategory_abelian`: the pair `⟨inferInstance, rfl⟩`.
  The abelian instance is Mathlib's instance on `P.FullSubcategory` in
  `Mathlib.CategoryTheory.Abelian.Subcategory`. It requires zero
  containment, closure under kernels and cokernels, and finite-product
  closure. Mathlib derives kernel closure from subobject closure and
  cokernel closure from quotient closure (`ObjectProperty/Kernels.lean`).
  The preadditive field of that instance is the preadditive instance found
  on the full subcategory, which is Mathlib's `Preadditive.fullSubcategory`.
  The required equality
  `a.toPreadditive = Preadditive.fullSubcategory (simpleSupportObjects S)`
  therefore holds by `rfl`, which Lean accepted.
- Instances `simpleSupportInclusion_preservesFiniteLimits` and
  `simpleSupportInclusion_preservesFiniteColimits`: the actual inclusion
  `simpleSupportInclusion S` is the full-subcategory functor `ι`.
  Mathlib's `ObjectProperty.preservesKernels_ι` and `preservesCokernels_ι`
  show that it preserves kernels and cokernels; these use the kernel and
  cokernel closure derived from the Serre-class instance. The inclusion
  preserves zero morphisms, and the supported subcategory is abelian by the
  previous item, so it has finite products, (co)equalizers and a zero
  object. `Functor.preservesFiniteLimits_of_preservesKernels` and
  `Functor.preservesFiniteColimits_of_preservesCokernels` then give
  preservation of all finite limits and colimits.

The main theorem fills the four conjuncts by discarding the source
hypotheses and applying the instances above, the abelian witness, and
the pair of preservation instances.

The instances are declared globally. They are unconditional facts about
the actual published predicate and inclusion, with no extra parameters.

## Reused work

The mono/epi transport lemmas and `simpleSubquotientClasses_subset_union`
are Worker 695's published module
`Langlands.CategoryTheory.Renard.SimpleSubquotientSubobjectQuotient`. The
support predicate, full subcategory and inclusion are the published
`Langlands.CategoryTheory.Renard.SimpleSupport`. From Mathlib, the proof uses
`ObjectProperty.IsSerreClass` (Joël Riou), the abelian full-subcategory
criterion in `CategoryTheory/Abelian/Subcategory.lean` (Justus Springer),
`ObjectProperty.prop_biprod` and `IsClosedUnderFiniteProducts.mk'`, the
kernel and cokernel preservation lemmas for `ι`, and the left/right
exactness criteria in `CategoryTheory/Preadditive/LeftExact.lean` (Markus
Himmel and Jakob von Raumer).

## Scope

Closure under arbitrary coproducts or colimits, the supported sums `E_S`
and their maximality, Hom orthogonality, splitting and product
decomposition are outside this unit.
