# Proof of the kernel/cokernel/finite-product criterion for abelian full subcategories

Author: Worker 894. This file proves the published statement
`Langlands.CategoryTheory.AbelianOfKernelsCokernelsFiniteProducts`
(module `Langlands.CategoryTheory.AbelianSubcategoryStatement`, by
Worker 633). The statement is unchanged and imported by its Lean name.

## Theorem

Module `Langlands.CategoryTheory.AbelianSubcategoryKernelsProof` contains

```lean
theorem Langlands.CategoryTheory.abelianOfKernelsCokernelsFiniteProducts_proof
    (C : Type u) [Category.{v} C] [Abelian C] (P : ObjectProperty C) :
    AbelianOfKernelsCokernelsFiniteProducts C P
```

It holds for every abelian category `C`, with independent object universe
`u` and morphism universe `v`, and for every object property `P`. Unfolded,
it says: if `P.ContainsZero`, `P.IsClosedUnderKernels`,
`P.IsClosedUnderCokernels` and `P.IsClosedUnderFiniteProducts` hold, then
`Nonempty (Abelian P.FullSubcategory)`. The full subcategory carries
Mathlib's induced category structure. The theorem adds no hypothesis. Its
axioms are `propext`, `Classical.choice` and `Quot.sound`.

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

This theorem is a deliberately strengthened sufficient correction derived
from Mathlib. It is not a verbatim assertion of the book. Kernel and cokernel
closure are weaker than closure under all subobjects and quotients.
Finite-product closure is the condition missing from the printed sentence.
The criterion is not claimed to be necessary, and it does not classify all
abelian full subcategories.

## Implemented proof

The proof introduces the four closure hypotheses. They are type classes, so
they become local instances. Mathlib's instance

```lean
instance [Abelian C] [P.ContainsZero] [P.IsClosedUnderKernels]
    [P.IsClosedUnderCokernels] [P.IsClosedUnderFiniteProducts] :
    Abelian P.FullSubcategory
```

in `Mathlib/CategoryTheory/Abelian/Subcategory.lean` (Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`) is then found by
`inferInstance`. The anonymous constructor packages it as
`Nonempty (Abelian P.FullSubcategory)`.

That Mathlib construction gets kernels and cokernels in the full
subcategory from `ObjectProperty.createsKernels` and `createsCokernels`,
and finite products from finite-product closure. It gets the
normal-monomorphism and normal-epimorphism axioms from the ambient ones,
through the inclusion functor. No Library result other than the statement
is used.

## Scope

This file proves only the first general criterion. It does not compare the
source's AB0–AB3* axioms with Mathlib's `Abelian`. The subobject/quotient
criterion, the concrete dimension-at-most-one counterexample and the book's
possibly nonunital module category are handled elsewhere. The file imports
only the statement module and adds no other file.
