# Exactness of actual nondegenerate dual pullbacks

`Langlands.Algebra.nonUnitalModuleDualMapExactnessStatement` proves exactly
`NonUnitalModuleDualMapExactnessStatement.{uA,uM,uN,uP}`. The theorem is
closed: the algebra, its structures and idempotentedness, three original
modules, their specified actions and nondegeneracy, and two intertwiners
are all quantified inside the published proposition. No target or imported
definition is changed.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The dual functors and exactness lemma are I.4.1, printed pages 22–23 /
PDF pages 28–29. The original nonunital conventions are printed pages 5–7 /
PDF pages 11–13; canonical complex scalars are I.2.1, printed page 14 /
PDF page 20; the fixed-part splitting is I.3.1, printed page 19 /
PDF page 25. These passages were read directly and the source hash checked.
The registered supplement `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read at PDF pages 1–2. Those nearby corrections do not change the
exactness lemma in the governing 2026 edition. No project errata file for
either source was found at this check.

The implemented argument uses full vector-space dual extension and an
idempotent projection. Renard instead identifies each fixed part with the
dual of the original fixed part and tests exactness there. This file uses
the actual published duals and pullbacks throughout and does not use or
reprove the separately owned fixed-part inverse, equivalence or naturality.
The helper lemmas are internal steps of this exactness proof.

First, `NonUnitalModuleDual.pullback_lift_of_full` starts with an actual
nondegenerate functional φ on M and a full-dual functional ψ on N satisfying
ψ(f(m)) = φ(m). Choose an original idempotent e fixing φ, using the published
`mem_dual_iff`. Replace ψ by the functional n ↦ ψ(e • n). Idempotence of e
makes the replacement fixed by e and therefore a member of the actual
nondegenerate dual subtype. Intertwining gives
ψ(e • f(m)) = ψ(f(e • m)) = φ(e • m) = φ(m), so it still lifts φ.

For `pullback_surjective_of_injective`, recover exactly each original
module's complex scalars with `NondegenerateScalars.complexModule` and use
`complexToLinearMap` on the given original intertwiner. Mathlib's
`LinearMap.dualMap_surjective_of_injective` supplies a full-dual extension;
the preceding helper makes it nondegenerate without changing its pullback.
The Mathlib theorem is unrestricted algebraic vector-space dual extension,
with no finite-dimensionality hypothesis.

For `pullback_injective_of_surjective`, equality after pullback is equality
of the original functionals at every f(m). Surjectivity of f gives equality
at every n, and extensionality of the actual subtype finishes the proof.

For `pullback_exact`, suppose the pullback of φ along f is zero. Exactness
of f,g says every element of the kernel of g equals f(m), so φ annihilates
that kernel. Mathlib's
`LinearMap.range_dualMap_eq_dualAnnihilator_ker` gives a full-dual ψ on P
with ψ ∘ g = φ. Apply the same idempotent adjustment to obtain a lift in
the actual nondegenerate dual of P. Conversely, every pullback along g
vanishes after pullback along f because g(f(m)) = 0. This proves
`Function.Exact D(g) D(f)` for the actual published pullbacks.

The closed theorem packages this middle-exactness assertion, both endpoint
reversals, and reversal of a short exact pair. The three implications and
short exact conclusion share the same specified original maps. The
separate endpoint proof files expose the same lemmas without a redundant
third original module.

All four universes are independent. The module actions may be nonunital;
only nondegeneracy and the original algebra hypotheses from the target
are used. The complex scalars are precisely the published recovered
scalars, and all local full-dual actions are the named `fullAction`.
There are no finite-dimensionality, admissibility, faithfulness,
nontriviality, chosen splitting or exactness-certificate hypotheses. Zero
algebras and zero modules remain in scope. Specialization to the opposite
algebra supplies the right-module original-map versions; the separate
categorical proof accounts for the actual right-to-left functor's
published double-opposite transport.

The proof and explanation originate with Worker 702. Worker 6's import
compatibility correction gives the three local `fullAction` instances
the explicit names `mapExactnessFullActionM`, `mapExactnessFullActionN`
and `mapExactnessFullActionP`. Previously their generated names collided
with those in the separately published `NonUnitalModuleBidualEvaluation`
when both import closures were loaded. Each named instance still has
exactly the same type and definition, and the argument above is unchanged.
The original-map target and every imported statement remain unchanged.
