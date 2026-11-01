# Filtered-colimit exactness for original nondegenerate modules: statements

This unit states the final assertion of the proposition in Renard I.6,
using the actual published category `NondegenerateModuleCat A` and its
original additive intertwining maps. It supplies two closed Prop-valued
targets and their conjunction. Neither target is proved here.

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, I.6 Proposition
and proof, printed pp.27–28 / PDF pp.33–34, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Both retained source pages were read in full. On printed p.28 the source
spells out the last assertion with three inductive systems M, N, P:
pointwise exact sequences 0 → M(i) → N(i) → P(i) → 0 induce an exact
sequence 0 → colim M → colim N → colim P → 0. It suggests comparison
with ambient module colimits, or repeating the ambient proof.

The targets have independent coefficient, index and residual module
universes uA, uI, uM. The actual category has carrier universe max uI uM,
which can contain colimits of diagrams whose objects and arrows are of
size uI. It does not enlarge carriers to the coefficient universe.
Every assertion quantifies over an arbitrary nonunital ring A and its
idempotented property hA. It locally installs the published abelian
structure `NondegenerateModuleCat.abelian A hA`.

`MathlibAB5Statement` asserts the existence of
`HasFilteredColimitsOfSize.{uI,uI}` and a certificate of
`CategoryTheory.AB5OfSize.{uI,uI}` for that very category. The certificate
is wrapped in `Nonempty` because Mathlib's class carries structure data;
the target itself is a proposition. The witness is installed locally so
that the certificate refers to the actual chosen colimit functors.
Mathlib's `HasExactColimitsOfShape` means that the colimit functor
preserves finite limits. In an abelian category, right exactness is
automatic for a colimit functor, so this expresses exactness. This is a
derived categorical formulation of the source's final assertion. It is
separate from Renard's earlier `SourceAB5` subobject-distributivity
predicate; no equivalence between those two generic predicates is asserted.

`ShortExactColimitsStatement` independently asserts filtered-colimit
existence. For every filtered category J of the stated object and arrow
size, it then quantifies over an actual short complex S in the functor
category J → NondegenerateModuleCat A. Its three objects are the three
systems and its two arrows are natural transformations, so compatibility
with transition maps is retained. The hypothesis says that evaluation
at every j is `ShortExact`. The conclusion is `ShortExact` for the image
under the actual Mathlib colimit functor. Thus it includes monicity of
the induced first arrow, exactness at the middle colimit, and epicity of
the second arrow. It does not replace short exactness with only middle
exactness or omit either endpoint condition. For a directed preorder
viewed as a category, this specializes to the source's displayed systems.
Allowing arbitrary filtered index categories is the disclosed categorical
extension of that concrete formulation.

The source's I.6 assumes an idempotented complex algebra. The extension
here to arbitrary idempotented nonunital rings is derived, rather than
attributed verbatim to the book: integer unitization retains each
original additive action and its underlying maps; filtered colimits of
unital modules are exact; and the actual nondegenerate inclusion is
exact and preserves colimits by its published adjunction. This explains
the intended wider scope and a proof route, and supplies no new proof.
No coefficient field, unit law for the original action, dimension bound,
Noetherianity, projectivity, generator or assumed exactness certificate
is a hypothesis. Both colimit existence and exactness are conclusions.

`FilteredColimitAssertions` conjoins the two targets. The examples expose
the complete unapplied targets as propositions, check all six distinct
universe-level permutations, and unfold the conjunction reflexively.
Proofs, general comparisons between source AB5 and Mathlib AB5, local
finite type/source AB6, the remainder of Chapter I and the whole book
remain separate obligations.
