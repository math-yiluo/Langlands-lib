# The prescribed natural dual-Hom equivalence

This statement family specifies the inverse identities and natural complex-linear
equivalence of the two actual dual-Hom spaces in Renard I.4.2.1. It imports the
published construction `NonUnitalModuleDualHomTranspose`. It introduces
Prop-valued targets and interface checks; it supplies no proof of those targets.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The unnumbered lemma and formula (I.4.2.1) are on printed p.24 /
one-based PDF p.30. The original nonunital conventions are on printed
pp.5–7 / PDF pp.11–13; canonical complex scalars and pointwise Hom
scalars are in I.2.1, printed p.14 / PDF p.20; the actual nondegenerate
dual is in I.4.1, printed pp.22–23 / PDF pp.28–29.

The original I.4.2.1 page was reread for this statement family. The
registered `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pp.1–2, addresses nearby adjunction, duality and admissibility
arguments. It does not replace the swap formula here; the 2026 edition
governs.

The source asserts that the swap
`psi(w)(v) = phi(v)(w)` is an isomorphism natural in the original
right module V and left module W. It proves the assertion through two
tensor-Hom identifications. This file specifies the same mathematical
identification through the already constructed maps `T` and `S`.
Whole-map inverse identities, precise scalar choices, equality with the
original additive maps and functions, and explicit squares over independent
universes are derived formulations of the source's identification.

All original structures are quantified: A has its specified nonunital
ring, complex module, scalar tower and commuting complex scalars, with
`hA : IsIdempotented A`. V has its specified additive group and original
right action of `Aᵐᵒᵖ`, with `hV`; W has its specified additive group and
original left action of A, with `hW`. No complex module on either
original carrier is an input.

The carriers are exactly the published `R hA hV hW` and `L hA hV hW`.
They are the original intertwiner types into the actual nondegenerate
dual subtypes, with the precise inherited full-dual action on the first
target and `rightDualAction` on the second. The latter is the published
double-opposite transport, not a chosen anti-involution. Every complex
linear map and equivalence in this file uses precisely `rModule` and
`lModule`, which are the canonical recovered target-scalar Hom modules.

`InverseIdentities` states `S.comp T = id` and `T.comp S = id` as
equalities of entire complex-linear maps.

`PrescribedEquivalence` states existence of a complex-linear equivalence
from R to L whose entire forward and inverse linear maps are exactly
T and S. Its additive maps are exactly `transposeAdd` and `reverseAdd`,
and its entire functions are `transpose` and `reverse`.
Consequently the full-functional and evaluation formulas of the
published maps remain the formulas of this equivalence. No arbitrary
isomorphism or independent replacement map can satisfy the target.

For original right and left intertwiners `f : V' → V` and `g : W' → W`,
`Naturality` states existence of complex-linear representatives r and l
of exactly the entire additive maps `Rfg` and `Lfg`. These additive
maps are the original precomposition and actual dual pullback
postcomposition from the construction. The same conclusion supplies
equivalences E and E' at the two carrier pairs, with forward maps T and
inverse maps S, and the two whole linear-map squares
`E'.toLinearMap.comp r = l.comp E.toLinearMap` and
`E'.symm.toLinearMap.comp l = r.comp E.symm.toLinearMap`.
Linearity of r and l, the equivalences and both squares are conclusions,
not assumptions. The prescribed forward maps determine each component,
so the naturality conclusion cannot select unrelated components.

`DualHomTranspose` closes all three predicates under every original
structure, nondegeneracy witness and intertwiner. The algebra and four
carrier universes are independent. Complete unapplied assignments check
the component and naturality interfaces, including the asymmetric
assignments (0,1,2,3,4) and (4,3,2,1,0). These assignments check typing;
they do not prove the predicates. Definitional equalities additionally check
the entire closed quantified body of `DualHomTranspose`, both at arbitrary
independent universes and at those two unequal assignments. Their `rfl`
proofs verify the statement's interface, without proving the mathematical
assertions it specifies.

The statements retain arbitrary dimension, zero algebras and zero
modules. They add no unit, faithful-action, nontriviality, finite
dimensionality, admissibility or reflexivity hypotheses. Proof and exact
target validation remain separate obligations. Fixed-part comparisons,
bidual injection, exactness, tensor-Hom and the other I.4.2 functor
comparisons are outside this statement family.

Worker 6 authored the initial statement pair. Worker 1187 checked the
original passages and published interfaces and added the complete closed-body
universe checks.
