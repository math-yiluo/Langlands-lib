# Renard A.IV.2: directed quotient universal properties and eventual zero

This statement unit covers the last two paragraphs of Appendix A.IV.2 in
David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, printed page 258 / PDF page 264. The preceding
ordered-system convention is on printed page 257 / PDF page 263. The
registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Both original pages were read, and PDF264 was visually inspected.

The supplementary author errata
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF18–19, were checked. The correction of the older edition's “limit” to
“colimit” is already incorporated in the governing 2026 direct-system
paragraph. No project source-errata file was present at the inspected base.

All declarations below are `Prop`-valued definitions in
`Langlands.Renard.FilteredColimit`. This unit states the conclusions; their
proof is a separate obligation.

## Published constructions and hypotheses

The file imports
[FilteredColimit.lean](FilteredColimit.lean), whose
[paired explanation](FilteredColimit.md) describes the actual objects.
`Carrier G f` is the literal quotient of `Σ i, G i` by equality at a common
later stage. `of G f i` is its canonical additive homomorphism.
`lift G f g hg` is the actual additive quotient lift, with its already
proved representative computation. No new unknown colimit or lift is assumed.

The quotient statements quantify over any partial order `I : Type uI`
with `IsDirectedOrder I` and `Nonempty I`, arbitrary abelian groups
`G i : Type uG`, and additive transitions `f i j h`. The `DirectedSystem`
premise says that self transitions are identities and successive transitions
compose. There are no injectivity, finiteness or generation restrictions.
The index and component universes are independent.

`diagram G f` lifts the factors to
`ULift.{uI} (G i)` in `AddCommGrpCat.{max uI uG}`. Its transitions are the
original transitions conjugated by the actual additive lift equivalences.
The vertex of `cocone G f` is the actual quotient group, and each leg
lowers the lifted factor and applies `of G f i`. Consequently the
categorical universal-property target has precisely these components,
transitions, vertex and legs.

## Source assertions

`QuotientColimitStatement` states
`Nonempty (IsColimit (cocone G f))`. The `Nonempty` wrapper makes the
universal-property target a proposition while retaining an actual
`IsColimit` witness as the required conclusion.

`CompatibleFamilyLiftStatement` spells out the source's compatible-family
factorization on the original groups, with target `H : Type uH` an arbitrary
abelian group. The target universe is independent of both input universes.
The compatibility equations are
`g j (f i j h x) = g i x`. The two conclusions say that the published
`lift G f g hg` composed with each `of G f i` equals `g i`, and that any
additive homomorphism from the quotient satisfying these same equations
equals that lift. Thus the witness and its uniqueness are explicit.

The source describes this as the colimit universal property. The
factorization and uniqueness target expands that property; it is not an
additional premise. Its independent target universe also avoids restricting
the compatible-family conclusion to the fixed universe of the categorical
diagram.

`EventualZeroStatement` is the source's final assertion: if
`of G f i x = 0`, there exist `j` and `hij : i ≤ j` such that
`f i j hij x = 0`. The later stage is allowed to be `i` itself, as in the
source. The witness is a forward transition of the given representative.

## Derived comparison and the empty case

`EventualZeroIffStatement` adds the converse of the source implication and
states the resulting equivalence. That converse follows from the
canonical maps' transition compatibility and preservation of zero. It is
a derived strengthening, not a second assertion attributed to the text.

The source defines directedness by pairwise upper bounds, which permits
an empty index. The published `carrier_isEmpty` proves that the literal
disjoint-union quotient is then empty and cannot carry a group identity.
Thus the explicit `Nonempty I` premise is necessary for that concrete
group construction. This is an internal source-boundary correction,
rather than an author-issued erratum.

`EmptyColimitStatement` retains the empty categorical case: for any empty
partially ordered index, the published `emptyCocone G f`, with singleton
abelian group `PUnit` as its vertex and vacuous legs, is colimiting.
This is an internal completion of the empty-index boundary. It has an
`IsEmpty I` premise and no `Nonempty I` premise. Pairwise directedness is
unnecessary for this empty-diagram target. The actual diagram still has
the original groups and transitions with their intrinsic system laws.
The already published arbitrary-category ordered-system statements keep
their unrestricted index scope.

`FilteredColimitStatements` conjoins the five targets in the order above.
The empty-index completion and the derived converse are explicitly
distinguished from the source assertions. This unit does not assert a
proof or completion of Appendix A.IV or of the whole-book program.

Worker 709 authored the statements over the published construction.
Worker 6 contributed the source-scope reconciliation and retention of the
concrete quotient and empty-index obligations. Both contributions are
retained in the authorship of this successor.
