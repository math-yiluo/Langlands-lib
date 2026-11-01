# Completed submodule inclusion and Renard I.1.5.3

Authors: Worker 6 (statement definitions and interface checks) and Worker 1149
(audit against the original passage, accepted constructions and task contract).

This module defines three `Prop` targets. It proves none of the inclusion,
closedness or range assertions. Its `example` declarations check the complete
interfaces and definitional expansions of those targets, including their chosen
structures and universe parameters.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The relevant reading is Chapter I conventions and I.1.1–I.1.5, printed
pp.5–11/PDF11–17. The remark following the I.1.5 proposition, at printed
p.11/PDF17 and formula (I.1.5.3), says that a submodule's completion is its
closure in the ambient completion and gives the two displayed descriptions
of that subset. The nondegenerate ambient module is part of this remark's
hypotheses. Earlier Chapter I conventions allow rings without identity and,
even for rings with identity, actions for which identity need not act as the
identity map.

For the original data `A : Type uA`, `M : Type uM`, `NonUnitalRing A`,
`AddCommGroup M`, `NonUnitalModule A M`, `hA : IsIdempotented A`, and
`S : NonUnitalSubmodule A M`, write `L(T)` for the existing left-compatible
family carrier `NonUnitalModuleLeftLimit A T`. It consists of families of
original vectors with `e • x(e) = x(e)` and `e • x(f) = x(e)` whenever
`e ≤ f`. The carrier of `S` is the actual stable additive subgroup of `M`;
its additive structure and `A` action are the inherited ones from
`NonUnitalSubmodule`. No equivalence changes the original action.

Let `j = NonUnitalModuleLeftLimit.mapHom hA S.subtype`. This is the actual
completion of the original subtype intertwiner, from `L(S)` to `L(M)`.
Its coordinate at `e` is the original inclusion of `x(e)` into `M`. Let
`c = NonUnitalModuleLeftLimit.canonical (A := A) (M := M)`, the original
additive map with `c(m)(e) = e • m`.

Each per-action target explicitly installs both completed actions
`NonUnitalModuleLeftLimit.nonUnitalModule hA`, one for `S` and one for `M`.
It also installs the actual coordinate uniformities
`NonUnitalModuleLeftLimit.uniformSpace A S` and
`NonUnitalModuleLeftLimit.uniformSpace A M`, together with their associated
topologies. The uniformity is the infimum of the pullbacks of the discrete
original vector uniformities under each coordinate evaluation. Thus the
embedding assertion uses exactly these two uniformities, and closure and
closedness use exactly this topology on `L(M)`. No ambient topology parameter
or compatibility certificate enters either target.

`NonUnitalModuleCompletionSubmoduleInclusion hA M S` asserts the following
four conclusions as a conjunction:

- The whole additive map underlying `j` equals
  `NonUnitalModuleLeftLimit.mapAddHom S.subtype`.
- The function `j` is injective.
- The function `j` is a uniform embedding for the specified uniformities.
- The actual set `Set.range j` is closed in the specified topology on `L(M)`.

The injectivity, uniform embedding and closed-range package is an internal
explicit formulation of the identification of the completed submodule with
its image. It is not a separately numbered theorem in the source. It asserts
properties to prove; none of them is an input premise.

`NonUnitalModuleCompletionSubmoduleRange hA M S` asserts three literal set
equalities on the same existing ambient family carrier:

1. `Set.range j = closure (c '' (S : Set M))`.
2. `Set.range j = {x | ∀ e : Idempotent A, ∃ n : M,
   n ∈ S ∧ (e : A) • n = x.val e}`.
3. `Set.range j = {x | ∀ a : A, a • x ∈ c '' (S : Set M)}`.

The second equality spells out the original-coordinate condition
`x(e) ∈ e • S` in (I.1.5.3). Its witness is an original vector belonging to
the actual submodule. The third equality uses the specified actual completed
family action; its canonical image represents the source's inclusion of `S`
in the completion of `M`. All three equalities have the range of the same
actual completed inclusion as their left-hand side.

`NonUnitalModuleCompletionSubmoduleTheorem.{uA,uM}` is a closed proposition:
for every original scalar ring, its idempotentedness witness, every original
additive vector group and its original action, **if** `IsNondegenerate A M`,
then for every actual submodule `S` both per-action targets hold. It adds no
separate nondegeneracy assumption on `S`: a fixed idempotent for a vector of
`M` fixes that same vector in the inherited submodule. The per-action
propositions can be formed for an arbitrary original action; this formation
does not assert they hold, and the source-facing master retains precisely
the ambient nondegeneracy premise.

The scalar and vector universes are independent. `S` lives in `Type uM` and
both family carriers live in `Type (max uA uM)`. No equality of universes,
replacement carrier, unit-action law, nontriviality, field, commutativity,
countability, dimension, density or completeness assumption is required.
Zero rings and trivial groups remain admissible. A same-carrier original zero
action can instantiate each per-action target. Under such an action the
source-facing specialization still requires its original nondegeneracy
premise; the interface checks do not remove that premise.

The Lean examples check the complete unapplied interfaces of both per-action
propositions and the closed master at general independent universes and
at `(uA,uM) = (0,1)` and `(1,0)`. They also check the fully expanded bodies of
all three targets at all three assignments. Further expansions install
competing completed actions, uniformities and even topologies on the same
family carriers, and verify that the targets still expand to the specified
structures. The same-carrier original zero-action expansions check each
per-action proposition and their conjunction under the retained
nondegeneracy premise. These are definitional interface checks, not proofs
of the mathematical conclusions.

This is a focused statement unit. It consumes the actual coordinatewise
completion functor and actual left-family uniformity constructions by Lean
name. A separate proof successor must prove the eventual public master.
Recovery and faithfulness, the smoothing/completion adjunction, analytic
completion, right-ring completion, endomorphism descriptions and the rest of
I.1.5 and of the book remain separate obligations.
