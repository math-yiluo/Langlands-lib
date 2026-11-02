# Proof of the subobject/quotient/finite-product criterion for abelian full subcategories

Author: Worker 894. This file proves the published statement
`Langlands.CategoryTheory.AbelianOfSubobjectsQuotientsFiniteProducts`
(module `Langlands.CategoryTheory.AbelianSubcategoryStatement`, by
Worker 633). The statement is unchanged and imported by its Lean name.

## Theorem

Module `Langlands.CategoryTheory.AbelianSubcategorySubobjectsProof` contains

```lean
theorem Langlands.CategoryTheory.abelianOfSubobjectsQuotientsFiniteProducts_proof
    (C : Type u) [Category.{v} C] [Abelian C] (P : ObjectProperty C) :
    AbelianOfSubobjectsQuotientsFiniteProducts C P
```

It holds for every abelian category `C`, with independent object universe
`u` and morphism universe `v`, and for every object property `P`. Unfolded,
it says: if `P.ContainsZero`, `P.IsClosedUnderSubobjects`,
`P.IsClosedUnderQuotients` and `P.IsClosedUnderFiniteProducts` hold, then
`Nonempty (Abelian P.FullSubcategory)`. Subobject closure quantifies over
every ambient monomorphism `X ⟶ Y` and gives `P Y → P X`. Quotient closure
quantifies over every ambient epimorphism `X ⟶ Y` and gives `P X → P Y`.
The theorem adds no hypothesis. Its axioms are `propext`,
`Classical.choice` and `Quot.sound`.

## Source and correction

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, Appendix A.VI.1, printed page 261 / one-based PDF
page 267. Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, file
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
I reread PDF page 267 for this proof and confirmed the file hash. The page
says “Toute sous-catégorie pleine d’une catégorie A−mod stable par passage
aux sous-modules et aux quotients est encore une catégorie abélienne”. In
English: every full subcategory of A-mod closed under submodules and
quotients is again abelian. That sentence has no finite-product or
finite-sum hypothesis. The axioms AB0 and AB1 just below it do require a
zero object and finite products. The statement companion
`Langlands/CategoryTheory/AbelianSubcategoryStatement.md` records the full
source and errata checks.

This theorem keeps the printed sentence's subobject and quotient hypotheses
and adds zero containment and finite-product closure. It is a deliberately
strengthened sufficient correction derived from Mathlib, not a verbatim
assertion of the book. It is not claimed to be necessary. The
dimension-at-most-one counterexample stated as
`Langlands.CategoryTheory.DimensionLEOneNotAbelian` shows that the
finite-product hypothesis cannot be dropped.

## Implemented proof

The proof introduces the four hypotheses as local instances. It then derives
kernel and cokernel closure from two Mathlib instances in
`Mathlib/CategoryTheory/ObjectProperty/Kernels.lean` (Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`):

- `[P.IsClosedUnderSubobjects] : P.IsClosedUnderKernels`. The leg `k.ι` of
  a limit kernel fork is a monomorphism, so the kernel object lies in `P`
  whenever the source does.
- `[P.IsClosedUnderQuotients] : P.IsClosedUnderCokernels`. The leg `k.π` of
  a colimit cokernel cofork is an epimorphism, so the cokernel object lies in
  `P` whenever the target does.

With these two facts recorded by `have`, `inferInstance` finds Mathlib's
instance `Abelian P.FullSubcategory` from
`Mathlib/CategoryTheory/Abelian/Subcategory.lean`. That instance needs zero,
kernel, cokernel and finite-product closure. The anonymous constructor
packages it as `Nonempty (Abelian P.FullSubcategory)`. The proof does not
import the kernel/cokernel criterion's proof module. No Library result other
than the statement is used.

## Scope

This file proves only the second general criterion. It does not compare the
source's AB0–AB3* axioms with Mathlib's `Abelian`. It does not embed unital
`ModuleCat` into the book's possibly nonunital module category; that
remains a separate adapter obligation. The file imports only the statement
module and adds no other file.
