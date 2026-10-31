# Ambient abelianness of original additive nonunital modules

Workers 6 and 633. Worker 6 prepared the shared proof draft; Worker 633 checked
the transfer implementation and complete construction interfaces. This pair proves the published closed proposition
`Langlands.Algebra.NonUnitalModuleAmbientAbelianStatement.{uA,uM}` and supplies
the named instance `Langlands.Algebra.NonUnitalModuleCat.abelian.{uA,uM} A`.

The only input to the named instance is an arbitrary type `A : Type uA`
with its given `NonUnitalRing A` structure. The carrier universe `uM`
remains independent. The category is the published `NonUnitalModuleCat`;
its objects retain the original additive groups and actions and its maps
remain the original additive intertwiners. Zero rings, zero carriers,
and zero actions on nonzero additive groups, even over unital rings,
are admitted. No unit-action law, field, nondegeneracy, idempotentedness,
nontriviality or finiteness condition is added.

## Implemented proof

The proof imports the unchanged public statement and reuses its
`NonUnitalModuleAdditive` dependency. That dependency already supplies
the named pointwise `Preadditive` structure, finite products, and additive
extension and restriction functors for the integer-unitization equivalence.
The named instance applies Mathlib's `CategoryTheory.abelianOfEquivalence`
to the actual published `IntegerUnitization.extendFunctor A`, with target
`ModuleCat.{uM} (Unitization ℤ A)`. The ordinary module category is abelian
by Mathlib. No ambient Abelian structure is an input.

The transfer constructor retains the existing preadditive structure.
Consequently `NonUnitalModuleCat.abelian_toPreadditive` proves by reflexivity
that the resulting `toPreadditive` is exactly
`NonUnitalModuleCat.preadditive A`, including the pointwise Hom groups.
The theorem `nonUnitalModuleAmbientAbelianStatement` introduces the arbitrary
ring and witnesses the public existential with this named structure and
equality. Its complete unapplied type is precisely the public statement,
with no additional parameter or hypothesis. Examples check the complete
named-instance and agreement-theorem interfaces, instance inference, and both unequal universe cases
`(uA,uM) = (0,1)` and `(1,0)`.

## Provenance and boundary

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original conventions at printed pages 5–6 / PDF pages 11–12,
I.1.2 at printed page 7 / PDF page 13, A.VI.1 at printed page 261 /
PDF page 267, and A.VI.2 property 6 at printed page 262 / PDF page 268
were read directly when preparing the published statement and shared draft. The conventions allow nonunital rings and actions without a
unit law. A.VI.1 motivates the ambient module category, while property 6
describes additive Hom groups and distributive composition.

The exact existential formulation, equality of structures, and transfer
through integer unitization are internal derived content already identified
in the public statement. The implemented proof follows the published
equivalence and pinned Mathlib transfer constructor, rather than a source
proof of the ambient assertion. The statement's source audit distinguishes
the corrected 2026 edition from the separate registered 2010 errata and
records its author-page checks. The current Library note
`notes/renard/appendix-a-corrections.md` explains why the source's
full-subcategory assertion lacks a finite-product hypothesis.
That assertion is not used here: the original category's finite products
were already constructed through the unitization equivalence.

This proof establishes ambient abelianness with the exact pointwise
preadditive data. It does not supply concrete selected kernel/cokernel
formulas, their comparison maps, images/coimages or algebraic exactness
comparisons, nondegenerate-subcategory closure or abelianness, part-functor
exactness, an equivalence with the source's AB axioms, or complex-linear
and tensor comparisons. Those remain separate obligations.
