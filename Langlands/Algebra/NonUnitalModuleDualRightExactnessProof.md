# Right-to-left categorical exactness of the actual nondegenerate dual

This helper module supplies the right-module orientation of the categorical
proof of Renard I.4.1. It uses exactly the published
`NonUnitalModuleDual.rightToLeftFunctor`, including
`fromDoubleOppositeFunctor`, and the named
`NondegenerateModuleCat.abelian A hA` and
`NondegenerateModuleCat.abelian Aᵐᵒᵖ hA.op` structures. Their Hom groups are
the original inherited pointwise groups.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The source constructs both orientations at I.4.1, printed page 22 / PDF
page 28, and proves reversal of short exact sequences at printed page 23 /
PDF page 29. The original nonunital conventions and nondegeneracy are
printed pages 5–7 / PDF pages 11–13; recovered scalars are I.2.1, printed
page 14 / PDF page 20; the fixed-part splitting is I.3.1, printed page 19 /
PDF page 25. These passages and the supplementary
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pages 1–2, were read directly. The supplement does not change the
exactness assertion in the governing edition. No project errata files
for these registered sources were found.

The proof reuses the original-map lemmas `pullback_exact`,
`pullback_injective_of_surjective`, and
`pullback_surjective_of_injective` from
`NonUnitalModuleDualMapExactnessProof`, specializing the algebra to
`Aᵐᵒᵖ`. That module uses unrestricted complex-dual extension and projection
by a fixing idempotent. Thus the implemented route differs from Renard's
fixed-part equivalence route, and assumes or proves no fixed-part inverse,
equivalence, or naturality assertion.

`rightToLeft_additive` applies the published `pullback_add` over
`Aᵐᵒᵖ` and `fromDoubleOppositeMap_add`. Both are statements for the
original pointwise Hom groups, so their composition proves additivity of
the actual right-to-left functor.

`rightToLeft_mono_of_epi` and
`rightToLeft_epi_of_mono` use the published
`NondegenerateModuleExactnessConcrete.epi_iff` and `mono_iff` to convert
boundary categorical assumptions to surjectivity and injectivity of the
original intertwiners. The corresponding original-map reversal over
`Aᵐᵒᵖ` gives injectivity or surjectivity of the actual dual pullback.
The same concrete criteria, now over `A`, give the required left-module
monomorphism or epimorphism. The double-opposite transport changes the
action through `a ↦ op (op a)` and retains the function, so the criteria
apply directly.

`rightToLeft_exact` first converts categorical exactness of a
right-module short complex to `Function.Exact` for its actual original
intertwiners, reusing `original_functionExact_of_exact` from the companion
left helper module. The existence of lifts is the published concrete
exactness criterion; the reverse implication follows by evaluation of the
short complex's zero-composition identity. `pullback_exact` over `Aᵐᵒᵖ` supplies
the reversed function exactness. Applying the concrete criterion over
`A` proves exactness of `S.op.map (rightToLeftFunctor hA)`. This requires
only middle exactness, with no assumption on the two boundary arrows.

`rightToLeft_shortExact` combines that exactness with both
boundary reversals: the original last epi gives the dual first mono, and
the original first mono gives the dual last epi.

`rightToLeft_sequenceExact` proves both Renard one-sided conditions.
A short complex in the opposite right-module category is unopposed, and
its exactness and boundary condition unoppose with it. The preceding
exactness and endpoint reversal theorems give the required image exactness
and boundary condition. This theorem installs exactly the two named
abelian structures used by the closed categorical target.

The algebra and carrier universes are independent throughout. The original
additive groups, actions, recovered complex scalars and actual nondegenerate
dual subtypes are retained. No finite-dimensionality, admissibility,
nontriviality, unital action, faithfulness, replacement duality, fixed-part
equivalence or exactness certificate is assumed. This is a derived helper
module for the categorical closed target, not a separate proof submission
of a new target. The left orientation and final closed-target packaging
are provided in the companion categorical proof module.
