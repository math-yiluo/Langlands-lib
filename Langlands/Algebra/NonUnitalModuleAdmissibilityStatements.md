# Admissibility and the actual nondegenerate dual

Worker 6 supplied the statement draft. Worker 1149 audited the original source
and published interfaces, added the exact-structure checks, and clarified the
interpretation of simplicity.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, I.5.1, the unnumbered proposition and
corollary on printed page 26 / PDF page 32. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original page was read. The registered corrections,
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF page 2, replace the converse of the reflexivity proof on the printed 2010
page 29. That corrected converse is already present in the 2026 reference.
It passes through the ordinary algebraic bidual of each fixed space.

All declarations retain the original possibly nonunital complex algebra `A`,
the explicit local-idempotent witness `hA`, and the original nondegenerate
left module `M` with witness `hM`. The coefficient laws on the algebra are
`Module ℂ A`, `IsScalarTower ℂ A A`, and `SMulCommClass ℂ A A`. No complex
module on `M` is supplied separately. Admissibility is the actual
`NonUnitalModuleAdmissible.IsAdmissible hA hM`: every original idempotent-fixed
space `NonUnitalModuleCorner.FixedPart e M` is finite-dimensional for exactly
`NonUnitalModuleCorner.complexModule hA hM e`.
The algebra and carrier universes vary independently.

`AdmissibleIffEvaluationBijective` states the source proposition. A module is
admissible if and only if the published canonical intertwiner
`NonUnitalModuleDual.evaluation hA hM` is bijective. Its target is exactly
`NonUnitalModuleDual.Bidual hA hM`, with the original `A` action transported
from the double opposite. Its included functional sends a nondegenerate
functional `φ` to `φ.val m`. Bijectivity of this bundled module homomorphism
expresses that the canonical inclusion is an isomorphism. It does not merely
assert the existence of some abstract self-isomorphism.

`AdmissibleDual` states the first conclusion of the source corollary: an
admissible module has admissible nondegenerate dual. The dual retains
`NonUnitalModuleDual.dualAction hA hM` over `Aᵐᵒᵖ`, with exactly the published
nondegeneracy witness and the corresponding canonical recovered fixed-space
scalars. The full algebraic dual is not substituted for its nondegenerate part.

`AdmissibleSimpleIffDualSimple` states the second conclusion: under
admissibility, `M` is simple if and only if its nondegenerate dual is simple.
Both sides use Mathlib's `CategoryTheory.Simple` in the actual original
nondegenerate module category, and the right side uses precisely the published
`NonUnitalModuleDual.dualObject`. The left object is
`⟨NonUnitalModuleCat.of A M, hM⟩` in `NondegenerateModuleCat A`; the right object
is its actual right dual, in `NondegenerateModuleCat Aᵐᵒᵖ`. These full
subcategories have the original additive intertwiners as morphisms.

The mathematical interpretation is the source's module simplicity:
an original stable additive subgroup of a nondegenerate module inherits a
fixing idempotent for each of its vectors, so it is again an object of this
category. Subobjects therefore express the usual original submodules, and
the categorical simplicity condition allows only the zero submodule and the
whole module. Mathlib's definition requires, for every monomorphism into the
object, that it be an isomorphism if and only if it is nonzero. In particular,
the identity of a zero object cannot satisfy this condition, so simplicity
excludes the zero module without an extra nonzero hypothesis. This explains
the chosen formulation; this statement unit does not supply a formal
equivalence theorem between categorical simplicity and a submodule-lattice
predicate, or assume any equivalence of dual module categories.

`AdmissibilityDuality` universally quantifies these three proposition families
and conjoins them. Complete unapplied signature examples check each individual
family at independent algebra and carrier universes, retaining all original
action and coefficient inputs; the aggregate is also checked as a proposition.
The additional reflexive unfolding checks pin the evaluation's exact bidual
and transported original action, the dual's selected opposite-ring action
and its canonical fixed-space scalar modules, and the two actual categorical
objects in the simplicity statement.
These declarations are statements only. Their proofs,
including the comparison with ordinary finite-dimensional biduals and the
source's annihilator argument for simplicity, remain separate obligations.
