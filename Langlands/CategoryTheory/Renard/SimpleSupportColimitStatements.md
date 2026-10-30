# Renard A.IX: colimits of supported objects

Authors: Worker 6 and Worker 1006. Worker 6 prepared the initial paired
draft. Worker 1006 checked the original passages, current public definitions
and adopted declarations, and prepared the submission. These are proposition
targets; no colimit-closure theorem is proved in this module.

The source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, A.IX, printed page 268 /
PDF page 274. The registered original is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
The complete page was read as text and checked visually against the original.
The source states that the full subcategory `M_S` is stable under colimits,
as well as subquotients and extensions, in a source Grothendieck category
satisfying source AB6. Worker 1006 read A.VI.3 on PDF269–270 as well. Worker 6 read the adjacent
source material on PDF269–270 and 273–275 in the preceding audit.

The registered supplementary `renard-2010-corrections-complements`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
belongs to a different edition. Worker 1006 rechecked its Appendix A PDF18–19;
the old-page310 supported-sum letter correction is already present in 2026.
This comparison supplies no correction to the colimit-closure assertion.
The public Appendix A correction note concerns other passages. No dedicated
source errata note was found in the current project or pinned Library notes.
On 29 October 2026, the live [author page](https://perso.pages.math.cnrs.fr/users/david.renard/)
and linked 2010 errata were byte-for-byte identical to the registered sources
`renard-author-page-2026-10-26` (SHA256
`143092e92be11be1b9c5a03bfc1e9e4538edb45f9a67d5fc8cc474b7b6dcd580`)
and `renard-2010-corrections-complements`. The book section labels the errata
as belonging to 2010 and provides no separate 2026 errata link. This is a
limited source check, not an assertion that no further errata exist.

## Parameters and actual constructions

The namespace is `Langlands.Renard`, with `C : Type u`,
`[Category.{v} C]` and `[Abelian C]`. The source family universe `w`,
diagram Hom universe `t`, ambient Hom universe `v` and ambient object
universe `u` are independent. Every component retains
`IsSourceGrothendieck.{w} C`, `SourceAB6 C`,
`S : Set (ObjectClass C)` and `S ⊆ simpleClasses C`.
No generator, separator, well-poweredness, finite length, concrete
category or additional smallness premise is present.

The unchanged public definitions come from
`Langlands.CategoryTheory.Renard.SimpleSupport`,
`Langlands.CategoryTheory.Renard.CompositionChains`,
`Langlands.CategoryTheory.Renard.LocallyFiniteType` and
`Langlands.CategoryTheory.RenardGrothendieckAxioms`. In particular,
`SourceAB6 C` is the source local-finite-type condition, distinct from
Grothendieck's Tohoku AB6. The unchanged public `HasSimpleSupport S X` means that all actual simple
subquotient classes of `X` lie in `S`. It uses the actual isomorphism
quotient of objects and all actual simple quotients of nested subobjects.
It is not a finite-length constituent set or an assumed closure certificate.

`SimpleSupportCoproductStatement C` quantifies over
`hG : IsSourceGrothendieck.{w} C` and obtains
`letI : HasCoproducts.{w} C := hG.1`.
For every `I : Type w` and actual family `F : I → C`, it states that
support of every `F i` implies support of the actual coproduct `∐ F`.
Every family, including the empty one, is included. No arbitrary large
family of ambient subobjects is introduced.

`SimpleSupportColimitStatement C` quantifies over every actual category
`J : Type w` with `[Category.{t} J]`, actual diagram `F : J ⥤ C`, and
actual cocone `c : Cocone F`. It states that `IsColimit c` and support
of every `F.obj j` imply support of the actual vertex `c.pt`. The
universal-property witness is a premise identifying a colimit; it does
not assume any support conclusion. This formulation covers any choice
of colimit, without fixing an ambient chosen one or asserting the
existence of all colimits at arbitrary diagram Hom sizes.

`SimpleSupportColimitClosureStatement.{w,t,v,u} C` is the conjunction of
`SimpleSupportCoproductStatement.{w,v,u} C` and
`SimpleSupportColimitStatement.{w,t,v,u} C`, in that order. All three declarations are `def` declarations
returning `Prop`.

## Source correspondence and universe boundary

The general cocone target is the source closure assertion. The coproduct
target is its discrete-diagram instance, exposed separately for reuse.
Allowing an independent diagram Hom universe is an internal extension:
the object index remains exactly at the supplied source family size.
The suggested proof uses only the coproduct indexed by the objects of
`J`: its canonical morphism to a colimit cocone vertex is epi. Quotient
closure then supplies support of that vertex. This route does not
require a coproduct indexed by all arrows of `J` or a premise that those
arrows are small.

For ordinary small diagrams the assertion has exactly the source
meaning. General colimit existence from coproducts and cokernels is
an ambient categorical prerequisite; this unit states stability of
actual colimits, and does not claim to have proved that existence theorem.
In particular, `w` is not replaced by `max u v`, and the object universe
is not used as an oversized family universe to trivialize the category.

## Proof boundary

No target is assumed by another target, and no proof is supplied here.
A later proof can import the independently published arbitrary
simple-subquotient sum identity, apply it to images of the actual
coproduct injections and use mono/epi transport. Finite Serre closure
and abelianness of the actual supported subcategory are separate units.
The supported-subobject sum, its support/maximality and categorical
splitting remain with their existing tasks.

The adopted entry module compiled without errors or warnings in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. Exact aggregate inspection returned
`Prop` and universe order `w, t, v, u`. A private probe printed all three
complete unapplied declaration types and bodies, their public defining
predicates, and the generated coproduct-existence argument; this last argument
uses the first conjunct of `hG`. The three targets depend only on the standard
axioms `propext`, `Classical.choice` and `Quot.sound`.

Elaboration and complete declaration inspection are development evidence;
semantic acceptance and publication require independent review.
