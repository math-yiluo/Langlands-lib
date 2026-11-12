# Renard III.3.1: compatible group actions on original test modules

This construction records the module-side data in Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, III.3.1 Definition, printed p.83 / PDF p.89: a
nondegenerate `D(X)`-module with a linear group action compatible
with the action on `D(X)`. The source is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

New declarations have prefix
`Langlands.Sheaf.Renard.CompatibleTestActions`.

`testTranslate g f` is the actual inverse pullback
`x ↦ f (g⁻¹ • x)` on the published
`Langlands.HarmonicAnalysis.PointwiseTestAlgebra.Carrier X`.
It uses the original locally constant function and its compact
support proof, transported along the homeomorphism given by
`g⁻¹`. `testRepresentation` bundles these operators as a
complex-linear left representation. Identity and multiplication
are proved pointwise from the action laws; linearity is pointwise
linearity. `testRepresentation_mul` records preservation of the
published pointwise multiplication. This is the pointwise
algebra `D(X)`, with no convolution operation substituted.

`CompatibleTestAction G X` contains an object of the published
`Langlands.Algebra.NondegenerateModuleCat (Carrier X)` and a
group representation on that object's *original* additive carrier.
The complex module structure is exactly the published
`NondegenerateScalars.module ℂ isIdempotented module.property`;
it is derived from the original test action, rather than
supplied independently. The compatibility field is the literal
covariance law

`ρ(g)(f • m) = (g · f) • ρ(g)(m)`.

It expresses an intrinsic law on the supplied module and action;
it is not a sheaf reconstruction, equivalence, or assumed
theorem conclusion. `complexModule` exposes the same canonical
complex structure.

Morphisms retain the original nondegenerate module morphism and
require it to commute with every group operator on every vector.
The category uses the existing module identity and composition.
The commutation law is closed under composition by rewriting the
two original commutation equations; the category laws follow
from the original module category. `toTestModule` forgets the
group action without altering any module or morphism.

Individual operator continuity suffices for these definitions.
Renard's intended specialization has a jointly continuous action
of a topological group on a locally compact Hausdorff totally
disconnected space. No theorem extending the III.3.1 sheaf/module
identification to more general spaces is asserted here.
The group, base-space and original-module universes are independent.
There is no smoothness or finite-dimensionality assumption on the
group representation in this data definition, as in the opening
identification of III.3.1. The actual equivariant sheaf/module
comparison remains a subsequent statement over the canonical
sheaf/module constructions.
