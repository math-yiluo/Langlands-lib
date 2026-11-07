# Subobject unions and Noetherianity for smooth representations

Worker 1582. This internal, derived construction supplies the order-theoretic
infrastructure used in proving Renard VI.7.5. It applies to every commutative
ring `R`, group `G` and supplied topology on `G`, with independent coefficient,
group and representation-carrier universes `uR`, `uG`, `uV`. There is no
local-field, reductive-group, nontriviality or finiteness assumption.

The source conventions are David Renard, *Représentations des groupes
réductifs p-adiques*, French version of 9 July 2026, Appendix A.I.2–A.I.3,
printed pages 248–249 / PDF pages 254–255. The motivating application is
VI.7.5, Proposition, printed page 186 / PDF page 192. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at `/home/taskhub/central-library/Renard--Representations des groupes
reductifs p-adiques (2026 version)--2026.pdf`. These passages were read in
the original source. The broader ring and group scope and the explicit
group-algebra union formula are derived here; they are not attributed to
Renard as separately stated assertions.

## Construction and implemented proofs

The existing `groupAlgebraSubobjectOrderIso A`, from
[RenardFinitenessProof](RenardFinitenessProof.md), identifies all actual
categorical smooth subobjects of `A` with all submodules of
`A.representation.asModule` over `MonoidAlgebra R G`. Every subrepresentation
of a smooth representation is smooth, so this identification imposes no
additional condition on the submodules.

`subobjectUnion A S` takes the supremum of the image of `S` in that complete
submodule lattice and transports it back through the inverse order
isomorphism. It is an actual categorical subobject of the original smooth
representation. `subobjectUnion_isLUB` transfers the submodule supremum's
least-upper-bound property back through the order isomorphism.
`groupAlgebraSubobjectOrderIso_subobjectUnion` gives the exact defining
submodule formula. Both statements include the empty subset.

`hasSubobjectUnions` packages this chosen least upper bound for each
subset. `hasAllSubobjectUnions` quantifies over every smooth object. These
are the published `Langlands.Renard.HasSubobjectUnions` and
`HasAllSubobjectUnions` predicates without modifying their definitions.

`renardNoetherian_iff` identifies
`Langlands.Renard.IsNoetherianObject A` with
`IsNoetherian (MonoidAlgebra R G) A.representation.asModule`. Its private
transport lemma sends a nonempty set of subobjects through an order
isomorphism, takes a maximal element there, and reflects both its membership
and maximality. Applying this lemma in both directions to
`moduleSubobjectOrderIso A` compares the two categorical predicates.
The published unital-module theorem
`Langlands.Renard.ModuleNoetherian.object_iff`, from
[RenardModuleNoetherianProof](../../CategoryTheory/RenardModuleNoetherianProof.md),
then gives the stated module predicate. Thus the proof uses Renard's
maximal-element definition directly, with no assumed equivalence or
stationary-chain hypothesis.

This module proves the all-unions part needed for the VI.7.5 Proposition.
It does not prove that finitely generated smooth representations are
Noetherian, that any smooth category is a Noetherian category, or that
parabolic induction preserves finite type. Those substantive assertions
remain the two exact targets of task
`ea93fe45-ec73-41a7-aca0-ff6d5a72aa23`.

Prepared environment: `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.
