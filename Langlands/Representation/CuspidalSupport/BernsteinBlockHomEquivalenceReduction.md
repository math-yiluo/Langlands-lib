# The categorical step in Renard VI.10.2

Author: Worker 85. Derived supporting construction for Task 5225.

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, VI.10.2, printed p.208 / PDF p.214, derives the
block's module-category equivalence from its finitely generated progenerator
of VI.10.1, using the categorical argument of VI.4.1 and A.VIII.2.
Registered source: `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

`bernsteinSaturatedBlockModuleEquivalence` constructs an actual equivalence
from the unchanged published `BernsteinSaturatedBlock` to
`ModuleCat (End P)ᵐᵒᵖ`, given a block object `P` satisfying the displayed
epimorphism-lifting, finite group-algebra generation and morphism-separation
conditions. The construction applies
`bernsteinSaturatedBlock_homEquivalence_of_finite_projective_generator`
from `BernsteinBlockCoproducts`. That module supplies the inherited abelian
structure, the Hom-sized coproducts and the finite-generation smallness
needed by the published generic small-progenerator theorem.

The forward functor is definitionally `preadditiveCoyonedaObj P`, as proved
by `bernsteinSaturatedBlockModuleEquivalence_functor`. The inverse is the
one selected by Mathlib from that functor's equivalence structure. No
identification with the tensor-product inverse is asserted.

`bernsteinBlockHomEquivalence_of_inducedProgenerator` proves the exact
implication from `BernsteinInducedProgeneratorStatement.{uF, uV}` to
`BernsteinBlockHomEquivalenceStatement.{uF, uV}`. After introducing every
published quantifier and premise, it takes the block-membership witness
and all three conclusions supplied by the first statement and applies the
objectwise categorical theorem. It adds no field, carrier-universe,
admissibility, finite-length, block-decomposition, support-uniqueness or
abelianness premise.

This is a conditional reduction: the full VI.10.1 proposition remains
an explicit premise. It does not prove the unconditional VI.10.1 or
VI.10.2 target and is not submitted as proof acceptance for either one.
Its provenance is the derived categorical application of the named
published generic constructions; the source supplies the mathematical
motivation and the same inference.
