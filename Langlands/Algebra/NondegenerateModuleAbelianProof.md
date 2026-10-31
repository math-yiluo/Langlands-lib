# Abelianness of the actual nondegenerate original-module category

Authors: Worker 6 and Worker 695. Worker 6 authored the shared proof draft.
Worker 695 checked the published dependencies and original passages, finalized
the explanation, and checked the complete declarations for submission.

`Langlands.Algebra.nondegenerateModuleAbelianStatement.{uA,uM}` proves the
entire published `NondegenerateModuleAbelianStatement.{uA,uM}`. For every
`A : Type uA` with `NonUnitalRing A` and `IsIdempotented A`, it produces an
`Abelian (NondegenerateModuleCat.{uA,uM} A)` whose preadditive projection
equals the inherited `Preadditive.fullSubcategory (nondegenerateProperty A)`.
The ring and carrier universes are independent.

The reusable declarations in `Langlands.Algebra.NondegenerateModuleCat` are
`abelian A hA` and `abelian_toPreadditive A hA`. The former is named abelian
data on the existing full subcategory. Its only inputs are the original ring,
its given `NonUnitalRing` structure, and `hA : IsIdempotented A`. The latter
proves the exact inherited-preadditive agreement by reflexivity. The Lean
file checks the full unapplied interfaces of both declarations and the closed
theorem at arbitrary independent universes and both unequal assignments
`(0,1)` and `(1,0)`.

The implementation applies the published
`Langlands.Algebra.nondegenerateModuleClosureStatement` to `A` and `hA`.
Its four conclusions give zero containment and closure under ambient
subobjects, quotients and finite products for `nondegenerateProperty A`.
The proof places those established conclusions in the local instance context;
none is an additional hypothesis of the construction. Mathlib's
`CategoryTheory.ObjectProperty.IsClosedUnderKernels` instance follows from
subobject closure, and its cokernel counterpart follows from quotient
closure. The instance in `Mathlib.CategoryTheory.Abelian.Subcategory` then
constructs abelian data on this actual full subcategory, using the already
published ambient abelian structure.

Mathlib's construction extends the inherited full-subcategory preadditive
structure. Thus `abelian_toPreadditive` is `rfl`, and the final closed theorem
packages the named construction together with this equality. The inherited
structure comes from `NonUnitalModuleCat.preadditive`: its Hom groups are
the pointwise abelian groups on the original additive intertwiners.
In particular, zero, addition and negation agree with the published original
Hom operations. The objects, morphisms and actions are those of the existing
`NondegenerateModuleCat` inside the existing `NonUnitalModuleCat`.

No original unit-action law, nontriviality, field, commutativity, dimension or
finiteness hypothesis is added. The ambient original category still allows
arbitrary additive actions, including zero actions; membership in the full
subcategory is exactly the published elementwise nondegeneracy property.
Zero rings and trivial carriers are included. There is no replacement
category or input abelian certificate.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original conventions are printed pp.5–6/PDF11–12; I.1.2, printed
p.7/PDF13, defines the nondegenerate full subcategory and asserts its
abelianness. A.VI.1 and A.VI.2 property 6, printed pp.261–262/PDF267–268,
give the abelian axioms and Hom addition. Worker 695 rechecked these
passages, visually checked PDF13, and verified the source hash.

The route through all four proved closure properties is an internal
derivation using Mathlib's sufficient theorem. The zero and finite-product
clauses supply the hypotheses omitted by the source's unrestricted
subobject/quotient criterion, whose defect is recorded in the published
`notes/renard/appendix-a-corrections.md`. That insufficient criterion is
not used. The supplementary registered
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was rechecked at PDF18–19; it concerns the earlier edition and does not
replace the governing source or the implemented closure argument.

This pair proves the specified abelianness and inherited-Hom agreement.
Exactness of the inclusion and nondegenerate-part functor, other adjunctions,
completion, scalar comparisons and the remaining book assertions are
separate obligations.
