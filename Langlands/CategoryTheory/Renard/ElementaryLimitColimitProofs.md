# Proofs of Renard A.IV elementary limit and colimit characterizations

Author: Worker 1158.

This module proves the eight supplied-cone and supplied-cocone
characterizations in
[`ElementaryLimitColimitStatements`](ElementaryLimitColimitStatements.md).
The theorem `Langlands.Renard.ElementaryLimitColimit.elementaryLimitColimitStatements`
has exactly the closed type
`ElementaryLimitColimitStatements.{vC,uC,uI}`, with three independent
universe levels and no additional premises. The statement module and its
imports are unchanged.

The source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The first four examples are A.IV.1, printed pp.256–257 (one-based
PDF262–263); their named duals are in A.IV.2, printed p.257 (PDF263).
These pages were read for this proof. The statement companion records
the source's variable typo in the terminal example and the colimit
prose's reversed arrows. The proofs retain its corrected conventions:
factors into a limit vertex and factors out of a colimit vertex.

The proofs below are internal derivations of the published statements
using Mathlib's actual cones and cocones and its specialized universal
property APIs. They do not rely on the source's incorrect constant-functor
fullness assertion for a merely nonempty index category. The source
corrections and their scope are explained in the published
[Appendix A audit](../../../notes/renard/appendix-a-corrections.md).

## Empty diagrams

`emptyLimitStatement` transports `IsLimit t` to `IsTerminal t.pt` by
`isLimitEquivIsTerminalOfIsEmpty`. The terminal object's `from` supplies
an arrow from every object, and its `hom_ext` proves uniqueness. In the
reverse direction, choose the arrow from each explicit unique-existence
assertion. Its uniqueness clause supplies `IsTerminal.ofUniqueHom`;
the inverse of the same equivalence then supplies `IsLimit t`.

`emptyColimitStatement` implements the dual proof explicitly, using
`isColimitEquivIsInitialOfIsEmpty`, `IsInitial.to`, `IsInitial.hom_ext`
and `IsInitial.ofUniqueHom`. The arbitrary supplied empty diagram and its
vertex are retained, including its independent index universe.

## Kernels and cokernels

`kernelStatement` uses `KernelFork.IsLimit.lift'` to obtain the factor of
every arrow whose composite with `f` is zero, together with its
factorization equation. Given another factor, its equation and that of
the chosen factor identify their composites with `i`.
`Fork.IsLimit.hom_ext` then identifies the factors. Conversely, choose
the factor for every compatible arrow. The factorization and uniqueness
clauses of the explicit unique-existence property give precisely the
three arguments of `KernelFork.IsLimit.ofι`: a lift, its equation and
its uniqueness. This constructs limiting data for the supplied fork.

`cokernelStatement` performs the outward version with
`CokernelCofork.IsColimit.desc'`, `Cofork.IsColimit.hom_ext` and
`CokernelCofork.IsColimit.ofπ`. It uses the equations `p ≫ l = q` and
`f ≫ q = 0` in their published directions. Both components keep the
separate `HasZeroObject` and `HasZeroMorphisms` instances; neither uses
additivity, abelianness or an existence assumption for all kernels.

## Products and coproducts

`productStatement` obtains the factor of a family by
`Fan.IsLimit.lift`, with every projection equation supplied by
`Fan.IsLimit.fac`. If a competing factor has the same projection
equations, `Fan.IsLimit.hom_ext` proves equality. For the converse,
apply the explicit unique-existence assumption to the vertex and
projections of every competing fan. Choosing these factors, their
equations and their uniqueness gives `Fan.IsLimit.mk`.

`coproductStatement` uses the corresponding `Cofan.IsColimit.desc`,
`.fac`, `.hom_ext` and `.mk` APIs with arrows out of the supplied
vertex. The index type is arbitrary in both proofs: no nonemptiness,
finiteness or smallness condition is introduced. This includes empty
and infinite families.

## Pullbacks and pushouts

`pullbackStatement` uses `PullbackCone.IsLimit.lift'` for each compatible
pair, obtaining both factorization equations. Equality after composing
with the two supplied projections follows from these equations for any
competing factor; `PullbackCone.IsLimit.hom_ext` proves uniqueness.
Conversely, each competing pullback cone supplies a compatible pair via
its `fst`, `snd` and `condition`. Choose its asserted unique factor.
The two equations and uniqueness under both equations are the arguments
of `PullbackCone.IsLimit.mk`, constructing limiting data for the
original cone.

`pushoutStatement` gives the explicit dual construction using
`PushoutCocone.IsColimit.desc'`, `.hom_ext` and `.mk`. The competing
cocone supplies `inl`, `inr` and `condition`; its factors go from the
supplied pushout vertex to that competing vertex.

## Assembly and scope

`elementaryLimitColimitStatements` assembles the eight closed proofs in
the exact published order: empty limit, kernel, product, pullback,
empty colimit, cokernel, coproduct, pushout. Classical choice turns
propositional unique-existence assertions into the witness data required
by `IsLimit` and `IsColimit`. All uniqueness arguments are restricted to
arrows satisfying the displayed factorization equations.

This proves characterizations of the supplied cones and cocones. It
does not assert existence of these shapes in every category. The general
`ConeBridge`, A.IV.1 examples 5–6 and their duals, concrete abelian-group
product/direct-sum constructions, filtered-colimit branches and
A.VI.2(7) remain with their existing owners. This module makes no claim
of A.IV, Appendix A or whole-book completion.
