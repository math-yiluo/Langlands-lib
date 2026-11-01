# Canonical injection into the actual nondegenerate bidual

Worker 6 authored the shared feasibility draft. Worker 490 checked the original
source and the published evaluation constructions and prepared this statement
pair for independent review.

This is a statement family over the published constructions in
`Langlands.Algebra.NonUnitalModuleBidualEvaluation` and
`Langlands.Algebra.NonUnitalModuleRightBidualEvaluation`. It does not prove the
separation or injectivity assertions.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
I.4.1, printed p.23 / one-based PDF p.29, states the unnumbered corollary giving
the canonical injection into the nondegenerate bidual. Its proof separates a
nonzero vector by a full complex-linear functional and composes that functional
with an idempotent fixing the vector to obtain an element of the actual dual.
The action and nondegeneracy conventions are on printed pp.5–7 / PDF pp.11–13,
the recovered complex scalars in I.2.1 on printed p.14 / PDF p.20, and the actual
duality construction in I.4.1 on printed pp.22–23 / PDF pp.28–29.

The registered supplement `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pp.1–2, explicitly corrects the older proof by requiring that the vector
being separated be nonzero. The predicates below include this condition.
The 2026 edition governs. No source-specific project errata file was found
at the source audit on 1 November 2026. The supplement's later admissibility and reflexivity
correction concerns a separate result.

All names below are in
`Langlands.Algebra.NonUnitalModuleBidualInjectionStatements`.

`LeftSeparation hA hM` states that every nonzero vector of the original left
module is detected by an element of `NonUnitalModuleDual.Dual hA hM`, through
its entire included full functional `φ.val`. `RightSeparation hA hM` states
the corresponding assertion for the original right action over `Aᵐᵒᵖ`, using
`Dual hA.op hM`. These predicates record the separation assertion in the source
proof as its own reusable conclusion.

`LeftEvaluationInjective hA hM` conjoins injectivity of the exact published
`evaluation hA hM` and `evaluationLinear hA hM`. The target is the actual
`Bidual hA hM` with `bidualAction hA hM`, the specified double-opposite
transport. The linear map uses precisely
`NondegenerateScalars.complexModule hA hM` on the source and the module
recovered from `bidual_isNondegenerate hA hM` on the target.

`RightEvaluationInjective hA hM` conjoins injectivity of the exact
`rightEvaluation hA hM` and `rightEvaluationLinear hA hM`. These maps land in
`RightBidual hA hM` with `rightBidualAction hA hM`: the first dual action is
transported back to the original algebra before it is dualized again. Thus
this clause retains the actual right-to-left-to-right construction. It uses
the recovered complex modules `NondegenerateScalars.complexModule hA.op hM` and
`NondegenerateScalars.complexModule hA.op
  (rightBidual_isNondegenerate hA hM)` for the original right action and its
actual right bidual. The already published comparison identifies this evaluation
with the transported opposite-algebra evaluation and preserves its formula
`(rightEvaluation hA hM m).val φ = φ.val m`.

`EvaluationMonomorphisms hA` states that every component of the exact
`NonUnitalModuleDual.evaluationNatTrans hA` and
`NonUnitalModuleRightBidual.rightEvaluationNatTrans hA` is a categorical
`Mono`, in the original left and right nondegenerate module categories.
Their targets are the published `bidualFunctor hA` and
`actualRightBidualFunctor hA`. This is the categorical formulation derived
from the source's injection; it assumes no replacement evaluation map,
functor or equivalence.

`BidualInjection` is the closed `Prop` universally quantifying the specified
nonunital complex algebra, its idempotentedness, every original left module,
every original right module, and their nondegeneracy witnesses. It concludes
both separation predicates, all four injectivity assertions and both families
of categorical monomorphisms. The algebra and module universes `uA` and `uM`
are independent; the left and right module quantifiers are separate.
Only the algebra has a complex module structure as an input. Complex scalars
on the original module carriers are recovered from their original actions.
The statements retain arbitrary dimension and the zero algebra/module cases.

The complete unapplied interfaces are assigned to explicitly written
telescopes. The closed target is compared with its complete quantified body
by definitional equality. These checks are repeated with the algebra below
the module universe and with the module below the algebra universe. They
verify the proposition interfaces and universe order; they supply no proof
of separation, injectivity or monomorphy.

The evaluation constructions and naturality laws are reused as published.
The linear and categorical formulations are derived packaging of the
canonical injection on those exact constructions. Proofs of the present
closed target require a separate successor after independent statement
publication. Fixed-part duality, full-dual/corner comparisons, I.4.2 and
I.4.3 remain separate units.
