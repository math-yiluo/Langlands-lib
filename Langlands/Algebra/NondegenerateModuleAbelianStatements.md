# Abelianness with the inherited original Hom groups

Authors: Worker 6 and Worker 695. Worker 6 authored the statement and initial
companion; Worker 695 rechecked the original passages, published interfaces and
complete universe checks for submission.

`NondegenerateModuleAbelianStatement.{uA,uM}` requires that the actual
published nondegenerate full subcategory is abelian, with the preadditive
structure inherited from the published pointwise original Hom groups:

```lean
∀ (A : Type uA) [NonUnitalRing A], IsIdempotented A →
  ∃ h : CategoryTheory.Abelian (NondegenerateModuleCat.{uA,uM} A),
    h.toPreadditive =
      CategoryTheory.Preadditive.fullSubcategory
        (nondegenerateProperty.{uA,uM} A)
```

Here `nondegenerateProperty A` is the existing property on the existing
`NonUnitalModuleCat A`: each vector is fixed by an actual idempotent of
the acting ring. `NondegenerateModuleCat A` is its actual full subcategory.
Its morphisms are the published original additive intertwiners between
its objects. `Preadditive.fullSubcategory` inherits the given ambient
Hom groups along the inclusion, so zero, addition and negation are the
pointwise operations on those original intertwiners. The ambient
preadditive structure used in this expression is the published
`NonUnitalModuleCat.preadditive`, imported from
`Langlands.Algebra.NonUnitalModuleAdditive`.

Mathlib's `Abelian` contains data specifying a preadditive structure.
The equality in the conclusion therefore records more than existence
of unspecified abelian data: the resulting Hom groups must agree with
the inherited original ones. The file constructs no such data and
proves no abelianness theorem.

The only hypotheses are the arbitrary ring's given `NonUnitalRing`
structure and its finite-local-unit property `IsIdempotented A`.
The acting-ring universe `uA` and module-carrier universe `uM` are
independent. Complete definitional-equality checks expose the entire
closed body at arbitrary universes and at `(0,1)` and `(1,0)`.
The proposition has no original unit-action law, field, commutativity,
nontriviality, dimension or finiteness assumption. No abelian structure,
closure certificate, choice of fixing idempotents, product, kernel or
cokernel is supplied as an input.

The governing source is David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original module conventions on printed pp.5–6/PDF11–12 allow
nonunital rings and actions without a unit-action law.
I.1.2, printed p.7/PDF13, defines the actual nondegenerate category and
asserts that it is abelian after noting submodule and quotient closure.
A.VI.1, printed p.261/PDF267, lists the zero, finite-product, kernel,
cokernel and normality axioms; A.VI.2 property 6, printed p.262/PDF268,
describes addition of morphisms and distributivity of composition.
These original passages were read.

The existential packaging and exact equality with the inherited
preadditive structure are internally derived specification choices.
The source's unrestricted full-subcategory criterion is insufficient:
subobject and quotient closure alone do not ensure finite products.
The published `notes/renard/appendix-a-corrections.md` explains the defect
and a sufficient correction. The present proposition does not assume
that criterion. Its later proof can use the already published ambient
abelian structure together with separately proved zero containment and
subobject, quotient and finite-product closure for this specific
property. Mathlib's `ObjectProperty.Kernels` derives kernel and
cokernel closure from the subobject and quotient hypotheses, and
`Abelian.Subcategory` constructs the full-subcategory structure while
retaining its inherited preadditive operations. This file neither
proves nor assumes those closure results.

The supplementary `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was checked at PDF1–3 and PDF18–19 for the relevant module conventions
and Appendix A corrections. It concerns the earlier edition and does
not replace the governing original.

A separate proof unit must prove this exact statement and expose a
named abelian structure with the stated agreement. Exactness of the
inclusion and nondegenerate-part functor, the completion constructions
and adjunction, categorical comparison maps, complex scalar recovery,
and the remaining whole-book assertions are separate obligations.
