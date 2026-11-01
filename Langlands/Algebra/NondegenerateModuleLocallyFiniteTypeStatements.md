# Local finite type of actual nondegenerate modules

Authors: Workers 6 and 633. Worker 6 supplied the complete shared draft.
Worker 633 compared it with the original passages and published
interfaces, checked its closed targets, and prepared this submission.

This statement unit records Renard I.6's assertion that the original
nondegenerate module category is locally of finite type. It supplies
Prop-valued definitions, with no proof of the new assertions.

The governing source is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, I.6 Proposition
and proof, printed pp.27–28 / PDF pp.33–34. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Both retained source pages have been read in full; PDF p.34 was also
visually inspected to check the AB6 paragraph and footnote. The original
module and idempotented-ring conventions on PDF pp.11–13, the finite-type
definition on PDF pp.254–255, and the AB6 definition on PDF p.269 were
also read for this comparison. On printed p.28 the
source says that every object is an increasing sum of finite-type
objects, and footnote 3 calls this local finite type and distinguishes it
from Grothendieck's AB6. The published
`Langlands.CategoryTheory.Renard.LocallyFiniteType` follows A.VI.3,
printed p.263 / PDF p.269, with the actual finite-type convention of
A.I.3. Its paired Markdown documents that source reading and convention.
This unit reuses those predicates unchanged. The published
`notes/renard/appendix-a-corrections.md` concerns other passages and
was consulted. A bounded lookup in the workspace and current published
notes found no dedicated errata note for the governing source. The
registered supplementary `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read at PDF pp.18–19. Those pages concern the earlier edition and
contain no correction of the local finite-type definition; they do not
replace the 2026 source.

`DirectedFiniteTypeCoverStatement` ranges over every original
nondegenerate object M. It asks for a family F indexed by `Finset M.obj`
in the actual categorical subobject order, monotone under inclusion of
finite subsets. Each F(S), with Mathlib's actual chosen domain as object,
is source-categorically finite type. Every original vector in S must
lie in the range of the original additive intertwiner `(F S).arrow`.
Top must be the least upper bound of the entire range of F; this is a
conclusion and uses no assumed complete lattice. Finite subsets are
nonempty as a family and directed under union, so monotonicity makes
the family a nonempty directed increasing system. The explicit family
and vector-range condition implement the setwise increasing-sum proof
suggested by I.6. They are internal strengthening details, not a separate
numbered theorem from the source. No choice of a smaller skeleton or
arbitrarily small indexing type is asserted.

`SourceAB6Statement` asserts exactly the published
`Langlands.Renard.SourceAB6` of `NondegenerateModuleCat A` under its
named `NondegenerateModuleCat.abelian A hA` structure. Its full unfolding
says that top is the least upper bound of the set of all finite-type
subobjects of each object. It does not add AB5, a generator or
Noetherianity as a premise. Source finite type is the published
`IsFiniteTypeObject`, including arbitrary subobject unions and the
nonempty proper-chain condition. This unit does not redefine finite
type as finite generation or finite presentation.

The source assumes an idempotented complex algebra. These targets
explicitly extend to arbitrary nonunital idempotented rings with original
additive actions and intertwiners. The intended argument generates the
stable additive subgroup of each finite subset and uses the existing
source finite-generation comparison; closure under submodules supplies
nondegeneracy. These steps require neither complex coefficients nor a
unit or dimension hypothesis. The coefficient universe uA and original
carrier universe uM remain independent, and the explicit finite-subset
index lies in the carrier universe uM. No enlargement to max uA uM is
needed to form submodules of the fixed object.

`LocallyFiniteTypeAssertions` conjoins the explicit cover and the
canonical category assertion. Unapplied proposition examples and both
unequal coefficient/carrier universe specializations are included, as
is a reflexive unfolding check of the full canonical target. Proofs,
filtered-colimit exactness, and completion of I.6 or the whole book
remain separate obligations.
